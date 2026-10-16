import SpinGlass.Parisi.Concentration.GaussianCoordinateLaw

/-!
# Gaussian concentration under the physical disorder/root product law

Joint continuity of the tilted logarithm makes the exact Gaussian law
transport applicable to the observable and its expectation.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N k : ℕ} {J : Type*} [Fintype J]

/-- Continuous disorder, site-field and root-mark parameters give a continuous
actual logarithmic mass. The positive cascade marks are already integrated. -/
theorem continuous_pairHamLogTiltMass_of_continuous
    {Θ : Type*} [TopologicalSpace Θ]
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (lam : ℝ) {H : Θ → EnergySpace N} {a : Θ → Fin N × Fin 2 → ℝ}
    {z : Θ → Fin N × J → ℝ} (hH : Continuous H) (ha : Continuous a) (hz : Continuous z)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) :
    Continuous (fun θ : Θ =>
      pairHamLogTiltMass ms vs c (H θ) lam (a θ) K₀ K (z θ)) := by
  classical
  let V (θ : Θ) (σ : Fin 2 → Config N) :=
    pairBranchHamX N k (H θ) lam (a θ) K₀ K (z θ) 0 σ
  have hV (σ : Fin 2 → Config N) : Continuous (fun θ => V θ σ) := by
    unfold V pairBranchHamX pairBranchMark
    fun_prop
  apply continuous_iff_continuousAt.2
  intro θ₀
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  have hdiff (θ : Θ)
      (x : Fin k → Fin N × J → ℝ) (σ : Fin 2 → Config N) :
      pairBranchHamX N k (H θ) lam (a θ) K₀ K (z θ) x σ -
        pairBranchHamX N k (H θ₀) lam (a θ₀) K₀ K (z θ₀) x σ = V θ σ - V θ₀ σ := by
    simp [V, pairBranchHamX, pairBranchMark, mul_add, Finset.sum_add_distrib]
    ring
  have hb (θ : Θ) :
      |pairHamLogTiltMass ms vs c (H θ) lam (a θ) K₀ K (z θ) -
        pairHamLogTiltMass ms vs c (H θ₀) lam (a θ₀) K₀ K (z θ₀)| ≤
        2 * ∑ σ, |V θ σ - V θ₀ σ| := by
    apply abs_pairHamLogTiltMass_sub_le_of_hamiltonian_bound ms vs hc0 hc1 hcpos
      hsm hpos hlt
    intro x σ
    rw [hdiff]
    exact Finset.single_le_sum (fun τ _ => abs_nonneg (V θ τ - V θ₀ τ)) (Finset.mem_univ σ)
  have hcont : Continuous (fun θ => 2 * ∑ σ, |V θ σ - V θ₀ σ|) := by fun_prop
  apply squeeze_zero (g := fun θ => 2 * ∑ σ, |V θ σ - V θ₀ σ|)
    (fun θ => norm_nonneg _) ?_ ?_
  · intro θ
    simpa only [Real.norm_eq_abs] using hb θ
  · simpa only [sub_self, abs_zero, Finset.sum_const_zero, mul_zero] using hcont.tendsto θ₀

/-- Continuity of the actual logarithmic mass in the interaction disorder
and root marks jointly. The positive cascade marks are already integrated. -/
theorem continuous_pairHamLogTiltMass_disorder_root
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) :
    Continuous (fun θ : EnergySpace N × (Fin N × J → ℝ) =>
      pairHamLogTiltMass ms vs c θ.1 lam a K₀ K θ.2) := by
  exact continuous_pairHamLogTiltMass_of_continuous ms vs hc0 hc1 hcpos hsm hpos hlt
    lam continuous_fst continuous_const continuous_snd K₀ K

/-- The Gaussian fluctuation bound for the physical product law, rather
than only its standard-coordinate representation. Root marks here have
unit variance; physical root variances can be included in `K₀`. -/
theorem hasSubgaussianMGF_pairHamLogTiltMass_product
    {S : Matrix (Config N) (Config N) ℝ} (hS : S.PosSemidef)
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    {D d : ℝ} (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hdiag : ∀ σ, S σ σ ≤ (N : ℝ) * D) (hK : ∀ l, ∑ j, K₀ l j ^ 2 ≤ d) :
    let P := (multivariateGaussian 0 S).prod
      (Measure.pi fun _ : Fin N × J => gaussianReal 0 1)
    let F := fun θ : EnergySpace N × (Fin N × J → ℝ) =>
      pairHamLogTiltMass ms vs c θ.1 lam a K₀ K θ.2
    HasSubgaussianMGF (fun θ => F θ - ∫ θ', F θ' ∂P)
      (32 * (N : ℝ) * (D + d)).toNNReal P := by
  classical
  dsimp only
  let P := (multivariateGaussian 0 S).prod
    (Measure.pi fun _ : Fin N × J => gaussianReal 0 1)
  let F := fun θ : EnergySpace N × (Fin N × J → ℝ) =>
    pairHamLogTiltMass ms vs c θ.1 lam a K₀ K θ.2
  let G := pairGaussianLogTiltMass S ms vs c lam a K₀ K
  let Q := stdGaussian (EuclideanSpace ℝ (Config N ⊕ (Fin N × J)))
  have hF : Continuous F :=
    continuous_pairHamLogTiltMass_disorder_root ms vs hc0 hc1 hcpos hsm hpos hlt lam a K₀ K
  have hT := measurable_pairGaussianDisorderRoot (J := J) S
  have hLaw : Q.map (pairGaussianDisorderRoot S) = P := map_pairGaussianDisorderRoot hS
  have hmean : (∫ θ, F θ ∂P) = ∫ w, G w ∂Q := by
    rw [← hLaw, integral_map hT.aemeasurable hF.aestronglyMeasurable]
    rfl
  have hG := hasSubgaussianMGF_pairGaussianLogTiltMass hS ms vs hc0 hc1 hcpos
    hsm hpos hlt lam a K₀ K hD hd hdiag hK
  change HasSubgaussianMGF (fun w => G w - ∫ w', G w' ∂Q)
    (32 * (N : ℝ) * (D + d)).toNNReal Q at hG
  have hcomp (w) : F (pairGaussianDisorderRoot S w) = G w := rfl
  change HasSubgaussianMGF (fun θ => F θ - ∫ θ', F θ' ∂P)
    (32 * (N : ℝ) * (D + d)).toNNReal P
  have hmeas (s : ℝ) : AEStronglyMeasurable (fun θ => Real.exp (s * (F θ - ∫ θ', F θ' ∂P))) P :=
    (Real.continuous_exp.comp (continuous_const.mul (hF.sub continuous_const))).aestronglyMeasurable
  constructor
  · intro s
    rw [← hLaw]
    apply (integrable_map_measure (by simpa only [hLaw] using hmeas s) hT.aemeasurable).2
    simpa only [hLaw, hmean, Function.comp_def, hcomp] using hG.integrable_exp_mul s
  · intro s
    rw [mgf, ← hLaw, integral_map hT.aemeasurable (by simpa only [hLaw] using hmeas s)]
    simpa only [hLaw, hmean, hcomp, mgf] using hG.mgf_le s

end SpinGlass
