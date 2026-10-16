import SpinGlass.Parisi.Concentration.PairTiltProductConcentration
import Common.Mathlib.Probability.Distributions.Gaussian.HeatSemigroup

/-!
# Physical root variances in the Gaussian fluctuation bound

The exact root scaling transports the concentration estimate to every
nonnegative root variance, including the degenerate root law at zero.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- Centered concentration is invariant under an exact measurable law
transport. The map need not be injective. -/
theorem hasSubgaussianMGF_centered_of_measurePreserving
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {T : Ω → Ω'} (hT : MeasurePreserving T μ ν)
    {F : Ω' → ℝ} (hF : Measurable F) {c : ℝ≥0}
    (h : HasSubgaussianMGF (fun ω => F (T ω) - ∫ ω', F (T ω') ∂μ) c μ) :
    HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂ν) c ν := by
  have hmean : (∫ x, F x ∂ν) = ∫ ω, F (T ω) ∂μ := by
    rw [← hT.map_eq, integral_map hT.measurable.aemeasurable hF.aestronglyMeasurable]
  have hmeas (s : ℝ) : AEStronglyMeasurable (fun x => Real.exp (s * (F x - ∫ y, F y ∂ν))) ν :=
    (by fun_prop : Measurable _).aestronglyMeasurable
  constructor
  · intro s
    rw [← hT.map_eq]
    apply (integrable_map_measure (by simpa only [hT.map_eq] using hmeas s)
      hT.measurable.aemeasurable).2
    simpa only [hT.map_eq, hmean, Function.comp_def] using h.integrable_exp_mul s
  · intro s
    rw [mgf, ← hT.map_eq, integral_map hT.measurable.aemeasurable
      (by simpa only [hT.map_eq] using hmeas s)]
    simpa only [hT.map_eq, hmean, mgf] using h.mgf_le s

variable {N k : ℕ} {J : Type*} [Fintype J]

/-- Scaling the root marks is exactly the same as scaling the root factors,
before taking the branch partition function. -/
theorem pairHamG_scale_root (b : ℝ) (c : (Fin 2 → Config N) → ℝ)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) :
    pairHamG N k c H lam a (fun l j => b * K₀ l j) K z x =
      pairHamG N k c H lam a K₀ K (fun ij => b * z ij) x := by
  have he : pairBranchMark N k (fun l j => b * K₀ l j) K z x =
      pairBranchMark N k K₀ K (fun ij => b * z ij) x := by
    funext l i
    unfold pairBranchMark
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [pairHamG, pairBranchZX, pairBranchHamX, he]

/-- The same exact root scaling holds for the actual tilted logarithm. -/
theorem pairHamLogTiltMass_scale_root (b : ℝ) (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z : Fin N × J → ℝ) :
    pairHamLogTiltMass ms vs c H lam a (fun l j => b * K₀ l j) K z =
      pairHamLogTiltMass ms vs c H lam a K₀ K (fun ij => b * z ij) := by
  have he (c : (Fin 2 → Config N) → ℝ) :
      pairHamG N k c H lam a (fun l j => b * K₀ l j) K z =
        pairHamG N k c H lam a K₀ K (fun ij => b * z ij) := by
    funext x
    exact pairHamG_scale_root b c H lam a K₀ K z x
  simp only [pairHamLogTiltMass, pairHamConstrainedTiltMass, he]

/-- Independent standard root coordinates scale to the actual root law,
also when the target variance is zero. -/
theorem map_rootMarksLaw_sqrt (v : ℝ≥0) :
    (rootMarksLaw N (J := J) 1).map (fun z ij => Real.sqrt v * z ij) =
      rootMarksLaw N (J := J) v := by
  rw [Measure.pi_map_pi (fun _ => (measurable_const_mul _).aemeasurable)]
  simp only [gaussianReal_map_sqrt_mul]

/-- The Gaussian part of the weighted-mass concentration estimate under
the original root law. The variance proxy is $32N(D+v_0d)$ and is
independent of the number of positive cascade levels. -/
theorem hasSubgaussianMGF_pairHamLogTiltMass_root_variance
    {S : Matrix (Config N) (Config N) ℝ} (hS : S.PosSemidef)
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (v₀ : ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    {D d : ℝ} (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hdiag : ∀ σ, S σ σ ≤ (N : ℝ) * D) (hK : ∀ l, ∑ j, K₀ l j ^ 2 ≤ d) :
    let P := (multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)
    let F := fun θ : EnergySpace N × (Fin N × J → ℝ) =>
      pairHamLogTiltMass ms vs c θ.1 lam a K₀ K θ.2
    HasSubgaussianMGF (fun θ => F θ - ∫ θ', F θ' ∂P)
      (32 * (N : ℝ) * (D + (v₀ : ℝ) * d)).toNNReal P := by
  classical
  let T : EnergySpace N × (Fin N × J → ℝ) → EnergySpace N × (Fin N × J → ℝ) :=
    Prod.map id (fun z ij => Real.sqrt v₀ * z ij)
  have hT : MeasurePreserving T
      ((multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) 1))
      ((multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)) := by
    refine ⟨by fun_prop, ?_⟩
    dsimp only [T]
    rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id,
      map_rootMarksLaw_sqrt]
  have hK' (l : Fin 2) : ∑ j, (Real.sqrt v₀ * K₀ l j) ^ 2 ≤ (v₀ : ℝ) * d := by
    simp only [mul_pow, Real.sq_sqrt v₀.coe_nonneg, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hK l) v₀.coe_nonneg
  have hh := hasSubgaussianMGF_pairHamLogTiltMass_product hS ms vs hc0 hc1 hcpos
    hsm hpos hlt lam a (fun l j => Real.sqrt v₀ * K₀ l j) K hD
    (mul_nonneg v₀.coe_nonneg hd) hdiag hK'
  apply hasSubgaussianMGF_centered_of_measurePreserving hT
    (continuous_pairHamLogTiltMass_disorder_root ms vs hc0 hc1 hcpos hsm hpos hlt
      lam a K₀ K).measurable
  simpa only [T, Prod.map_fst, Prod.map_snd, id_eq, ← pairHamLogTiltMass_scale_root] using hh

end SpinGlass
