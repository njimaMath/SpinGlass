import SpinGlass.Parisi.Concentration.PairTiltMass
import SpinGlass.Parisi.Analytic.BoundedDifferences
import SpinGlass.Parisi.Analytic.FieldTruncation

/-!
# Bounded-field fluctuations of the logarithmic tilted mass

Condition on the interaction disorder and the root marks. The actual
logarithmic constrained tilted mass has coordinate oscillation at most
eight times the clipping cutoff, uniformly in these conditioned variables.
The resulting moment bound has a variance parameter proportional to volume.
The product-law combination is proved in `PairTiltCombinedConcentration`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The same external field is used in both replicas; a site change
therefore has coefficient four in the logarithmic tilted mass. -/
theorem abs_pairHamLogTiltMass_shared_field_sub_le {N k : ℕ} {J : Type*} [Fintype J]
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (H : EnergySpace N) (lam : ℝ) (a b : Fin N → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) :
    |pairHamLogTiltMass ms vs c H lam (sharedReplicaSiteField a) K₀ K z₀ -
      pairHamLogTiltMass ms vs c H lam (sharedReplicaSiteField b) K₀ K z₀| ≤
        4 * ∑ i, |a i - b i| := by
  have hb := abs_pairHamLogTiltMass_sub_field_le ms vs hc0 hc1 hcpos hsm hpos hlt H lam
    (sharedReplicaSiteField a) (sharedReplicaSiteField b) K₀ K z₀
  simp only [replicaSiteFieldDistance, sharedReplicaSiteField, Fin.sum_univ_two] at hb
  linarith only [hb]

/-- Changing one clipped field coordinate changes the actual logarithmic
mass by at most eight times the cutoff. -/
theorem abs_pairHamLogTiltMass_clipped_field_update_sub_le {N k : ℕ} {J : Type*} [Fintype J]
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (H : EnergySpace N) (lam : ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (x : Fin N → ℝ) (i : Fin N) (y : ℝ) :
    |pairHamLogTiltMass ms vs c H lam
        (sharedReplicaSiteField (fun j => Aristotle.clip R (Function.update x i y j))) K₀ K z₀ -
      pairHamLogTiltMass ms vs c H lam
        (sharedReplicaSiteField (fun j => Aristotle.clip R (x j))) K₀ K z₀| ≤ 8 * R := by
  classical
  have hb := abs_pairHamLogTiltMass_shared_field_sub_le ms vs hc0 hc1 hcpos hsm hpos hlt
    H lam (fun j => Aristotle.clip R (Function.update x i y j))
    (fun j => Aristotle.clip R (x j)) K₀ K z₀
  have hsum : (∑ j, |Aristotle.clip R (Function.update x i y j) - Aristotle.clip R (x j)|) =
      |Aristotle.clip R y - Aristotle.clip R (x i)| := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  rw [hsum] at hb
  have hclip : |Aristotle.clip R y - Aristotle.clip R (x i)| ≤ 2 * R := by
    have hh := abs_sub (Aristotle.clip R y) (Aristotle.clip R (x i))
    linarith [(Aristotle.clip_bounds hR y).1, (Aristotle.clip_bounds hR (x i)).1]
  linarith only [hb, hclip]

/-- Conditional on arbitrary fixed interaction disorder and root marks,
the actual logarithmic weighted product has a clipped-field MGF bound.
The field law is any probability measure and needs no exponential moments. -/
theorem integral_exp_pairHamLogTiltMass_clipped_field_le {N k : ℕ} {J : Type*} [Fintype J]
    (μh : Measure ℝ) [IsProbabilityMeasure μh]
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (H : EnergySpace N) (lam : ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (s : ℝ) :
    let F := fun a : Fin N → ℝ => pairHamLogTiltMass ms vs c H lam
      (sharedReplicaSiteField (fun i => Aristotle.clip R (a i))) K₀ K z₀
    Integrable (fun a => Real.exp (s * (F a - (∫ b, F b ∂externalFieldVecLaw N μh))))
      (externalFieldVecLaw N μh) ∧
      (∫ a, Real.exp (s * (F a - (∫ b, F b ∂externalFieldVecLaw N μh)))
        ∂externalFieldVecLaw N μh) ≤ Real.exp (8 * R ^ 2 * N * s ^ 2) := by
  classical
  dsimp only
  let F := fun a : Fin N → ℝ => pairHamLogTiltMass ms vs c H lam
    (sharedReplicaSiteField (fun i => Aristotle.clip R (a i))) K₀ K z₀
  have hF : Measurable F :=
    ((lipschitzWith_pairHamLogTiltMass_field ms vs hc0 hc1 hcpos hsm hpos hlt H lam
      K₀ K z₀).continuous.comp (by
        unfold sharedReplicaSiteField
        fun_prop)).measurable
  have hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ (fun _ : Fin N => 8 * R) i :=
    abs_pairHamLogTiltMass_clipped_field_update_sub_le ms vs hc0 hc1 hcpos hsm hpos hlt
      H lam K₀ K z₀ hR
  have hi : Integrable F (externalFieldVecLaw N μh) :=
    Aristotle.integrable_of_bounded_differences hF hosc measurable_id
  have hb := Aristotle.bounded_differences_mgf (fun _ : Fin N => μh) hF hi
    (fun _ => 8 * R) (fun _ => by positivity) hosc s
  have he : s ^ 2 * (∑ _i : Fin N, (8 * R) ^ 2) / 8 = 8 * R ^ 2 * N * s ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [he] at hb
  exact hb

end SpinGlass
