import SpinGlass.Parisi.Concentration.PairTiltRootVariance
import SpinGlass.Parisi.Concentration.PairTiltFieldConcentration
import SpinGlass.Parisi.Concentration.ProductSubGaussian

/-!
# Joint disorder and field fluctuations of the tilted mass

The physical interaction disorder, root marks and i.i.d. clipped field are
all averaged. The variance proxy is $N(32(D+v_0d)+16R^2)$, independently
of the positive cascade depth and the field law.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N k : ℕ} {J : Type*} [Fintype J]

/-- The actual tilted logarithm with one clipped field shared by both
replicas, on the full disorder/root/field product space. -/
noncomputable def pairHamClippedLogTiltMass (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    (c : (Fin 2 → Config N) → ℝ) (lam : ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (R : ℝ)
    (z : (EnergySpace N × (Fin N × J → ℝ)) × (Fin N → ℝ)) : ℝ :=
  pairHamLogTiltMass ms vs c z.1.1 lam
    (sharedReplicaSiteField (fun i => Aristotle.clip R (z.2 i))) K₀ K z.1.2

/-- Joint continuity includes the field coordinates as well as the
interaction disorder and root marks. -/
theorem continuous_pairHamClippedLogTiltMass
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (lam : ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (R : ℝ) :
    Continuous (pairHamClippedLogTiltMass ms vs c lam K₀ K R) := by
  apply continuous_pairHamLogTiltMass_of_continuous ms vs hc0 hc1 hcpos hsm hpos hlt
  · fun_prop
  · unfold sharedReplicaSiteField
    fun_prop
  · fun_prop

/-- Full product-law concentration for the actual tilted logarithm. The
proof supplies its integrability and derives the MGF bound from the Gaussian
covariance and the field cutoff, with no field moment assumption. -/
theorem integrable_and_hasSubgaussianMGF_pairHamClippedLogTiltMass
    (μh : Measure ℝ) [IsProbabilityMeasure μh]
    {S : Matrix (Config N) (Config N) ℝ} (hS : S.PosSemidef)
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (v₀ : ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (lam : ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    {D d R : ℝ} (hD : 0 ≤ D) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hdiag : ∀ σ, S σ σ ≤ (N : ℝ) * D) (hK : ∀ l, ∑ j, K₀ l j ^ 2 ≤ d) :
    let P := ((multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)).prod
      (externalFieldVecLaw N μh)
    let F := pairHamClippedLogTiltMass ms vs c lam K₀ K R
    Integrable F P ∧ HasSubgaussianMGF (fun z => F z - ∫ w, F w ∂P)
      ((N : ℝ) * (32 * (D + (v₀ : ℝ) * d) + 16 * R ^ 2)).toNNReal P := by
  classical
  have hF := (continuous_pairHamClippedLogTiltMass ms vs hc0 hc1 hcpos hsm hpos hlt
    lam K₀ K R).measurable
  have hs (a : Fin N → ℝ) := hasSubgaussianMGF_pairHamLogTiltMass_root_variance hS ms vs v₀
    hc0 hc1 hcpos hsm hpos hlt lam
    (sharedReplicaSiteField (fun i => Aristotle.clip R (a i))) K₀ K hD hd hdiag hK
  have hosc (θ : EnergySpace N × (Fin N × J → ℝ)) (a : Fin N → ℝ) (i : Fin N) (y : ℝ) :
      |pairHamClippedLogTiltMass ms vs c lam K₀ K R (θ, Function.update a i y) -
        pairHamClippedLogTiltMass ms vs c lam K₀ K R (θ, a)| ≤ (fun _ : Fin N => 8 * R) i :=
    abs_pairHamLogTiltMass_clipped_field_update_sub_le ms vs hc0 hc1 hcpos hsm hpos hlt
      θ.1 lam K₀ K θ.2 hR a i y
  have hh := integrable_and_hasSubgaussianMGF_prod_of_section_and_bounded_differences
    (fun _ : Fin N => μh) hF hs (fun _ => 8 * R) (fun _ => by positivity) hosc
  have he : (32 * (N : ℝ) * (D + (v₀ : ℝ) * d)).toNNReal +
      (∑ _i : Fin N, (8 * R) ^ 2 / 4).toNNReal =
      ((N : ℝ) * (32 * (D + (v₀ : ℝ) * d) + 16 * R ^ 2)).toNNReal := by
    have hsum : (∑ _i : Fin N, (8 * R) ^ 2 / 4) = 16 * (N : ℝ) * R ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hsum, ← Real.toNNReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [he] at hh
  exact hh

end SpinGlass
