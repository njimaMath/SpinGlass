import SpinGlass.Parisi.Concentration.ParisiTiltConcentration

/-!
# Integrability of the original pair pressures

The constrained and unconstrained log pressures are separately integrable
under the full disorder/root/i.i.d.-field law. Only the first field moment
is used, so their difference can be averaged and normalized by Fubini.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N k : ℕ} {J : Type} [Fintype J]

/-- Gaussian integrability at a fixed realized replica field, for any
nonempty indicator constraint and also for the unconstrained partition. -/
theorem integrable_log_cascadeRec_pairHamG_gaussian
    {S : Matrix (Config N) (Config N) ℝ} (hS : S.PosSemidef)
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (v₀ : ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, c σ = 1) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) :
    Integrable (fun θ : EnergySpace N × (Fin N × J → ℝ) =>
      Real.log (cascadeRec k ms (siteGaussianMarks (Fin N × J) k vs)
        (pairHamG N k c θ.1 lam a K₀ K θ.2)).toReal)
      ((multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)) := by
  classical
  let G := GaussianField.ofMultivariateGaussian hS
  obtain ⟨σ₀, hσ₀⟩ := hcpos
  have hcpos' : ∃ σ, 0 < c σ := ⟨σ₀, by rw [hσ₀]; exact one_pos⟩
  have hcoord (σ : Config N) : Integrable (fun H : EnergySpace N => H σ)
      (multivariateGaussian 0 S) := by
    refine G.integrable.norm.mono' (by fun_prop) (.of_forall fun H => ?_)
    exact PiLp.norm_apply_le H σ
  have hexp (σ : Fin 2 → Config N) :
      (∫⁻ H : EnergySpace N, ENNReal.ofReal (Real.exp (-(H (σ 0) + H (σ 1))))
        ∂multivariateGaussian 0 S) ≠ ∞ := by
    simpa only [G, GaussianField.ofMultivariateGaussian, one_smul, id_eq] using
      G.lintegral_ofReal_exp_neg_smul_add_ne_top 1 (σ 0) (σ 1)
  exact integrable_log_cascadeRec k _ ms _ _ hpos hle
    (measurable_pairHamG_branchParam N k c measurable_id lam a K₀ K)
    (fun θ x => pairHamG_pos N k hc0 hcpos' θ.1 lam a K₀ K θ.2 x)
    (fun _ _ => ENNReal.ofReal_ne_top)
    (lintegral_lintegral_pairHamG_ne_top N hc0 id measurable_id hexp lam a K₀ K v₀ vs)
    (lintegral_lintegral_enorm_log_pairHamG_ne_top N hc0 hc1 hσ₀ measurable_id hcoord
      lam a K₀ K v₀ vs)

theorem measurable_pairHamRandomFieldLogPressure
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (c : (Fin 2 → Config N) → ℝ)
    (lam : ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) :
    Measurable (pairHamRandomFieldLogPressure ms vs c lam K₀ K) := by
  apply (measurable_cascadeRec_prod k ms (siteGaussianMarks (Fin N × J) k vs) ?_).ennreal_toReal.log
  unfold Function.uncurry pairHamG pairBranchZX pairBranchHamX pairBranchMark sharedReplicaSiteField
  fun_prop

/-- First-moment site laws suffice for joint log-pressure integrability.
The reference Gaussian section is at zero field; the field error is at
most twice the sum of the absolute site fields. -/
theorem integrable_pairHamRandomFieldLogPressure
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {S : Matrix (Config N) (Config N) ℝ} (hS : S.PosSemidef)
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (v₀ : ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, c σ = 1) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (lam : ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) :
    Integrable (pairHamRandomFieldLogPressure ms vs c lam K₀ K)
      (((multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)).prod
        (externalFieldVecLaw N μh)) := by
  let P := (multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)
  let F := pairHamRandomFieldLogPressure ms vs c lam K₀ K
  let B := fun θ : EnergySpace N × (Fin N × J → ℝ) => F (θ, 0)
  have hB : Integrable B P := integrable_log_cascadeRec_pairHamG_gaussian hS ms vs v₀
    hc0 hc1 hcpos hpos hle lam (sharedReplicaSiteField 0) K₀ K
  have hs : Integrable (fun a : Fin N → ℝ => 2 * ∑ i, |a i|) (externalFieldVecLaw N μh) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro i _
    exact ((measurePreserving_externalFieldVec_apply N μh i).integrable_comp
      hμ.abs.aestronglyMeasurable).2 hμ.abs
  refine ((hB.abs.comp_fst (externalFieldVecLaw N μh)).add (hs.comp_snd P)).mono'
    (measurable_pairHamRandomFieldLogPressure ms vs c lam K₀ K).aestronglyMeasurable
    (.of_forall fun z => ?_)
  obtain ⟨σ₀, hσ₀⟩ := hcpos
  have hcpos' : ∃ σ, 0 < c σ := ⟨σ₀, by rw [hσ₀]; exact one_pos⟩
  have hb := abs_log_cascadeRec_pairHamG_sub_field_le hc0 hcpos' ms vs hpos hle z.1.1 lam
    (sharedReplicaSiteField z.2) (sharedReplicaSiteField 0) K₀ K z.1.2
  have he : replicaSiteFieldDistance (sharedReplicaSiteField z.2) (sharedReplicaSiteField 0) =
      2 * ∑ i, |z.2 i| := by
    simp only [replicaSiteFieldDistance, sharedReplicaSiteField, Pi.zero_apply, sub_zero,
      Fin.sum_univ_two]
    ring
  rw [he] at hb
  change ‖F z‖ ≤ |B z.1| + 2 * ∑ i, |z.2 i|
  change |F z - B z.1| ≤ 2 * ∑ i, |z.2 i| at hb
  rw [Real.norm_eq_abs]
  linarith only [hb, abs_sub_abs_le_abs_sub (F z) (B z.1)]

end SpinGlass
