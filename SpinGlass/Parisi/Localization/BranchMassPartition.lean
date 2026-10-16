import SpinGlass.Parisi.Localization.OverlapValues

/-!
# Normalization of the physical overlap atoms

Summing the exact overlap constraints recovers the unconstrained partition
at every Gaussian mark. The tilted masses therefore sum to one, and the
joint meeting masses sum to the corresponding mass increment.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N k : ℕ}

theorem sum_pairHamG_constraintR {J : Type*} [Fintype J]
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) :
    (∑ u ∈ parisiOverlapValues N, pairHamG N k (constraintR N u) H lam a K₀ K z x) =
      pairHamG N k (fun _ => 1) H lam a K₀ K z x := by
  classical
  unfold pairHamG pairBranchZX
  rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ =>
    Finset.sum_nonneg fun σ _ => mul_nonneg (constraintR_nonneg N u σ) (Real.exp_nonneg _))]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.sum_mul, sum_constraintR_parisiOverlapValues]

/-- The physical tilted overlap masses partition one at every fixed
interaction disorder, root mark and site field. -/
theorem sum_pairHamConstrainedTiltMass_constraintR {J : Type*} [Fintype J]
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z : Fin N × J → ℝ) :
    (∑ u ∈ parisiOverlapValues N,
      pairHamConstrainedTiltMass ms vs (constraintR N u) H lam a K₀ K z) = 1 := by
  classical
  let G := pairHamG N k (fun _ => 1) H lam a K₀ K z
  let A := fun u x => pairHamG N k (constraintR N u) H lam a K₀ K z x / G x
  let μs := siteGaussianMarks (Fin N × J) k vs
  have hG : Measurable G := measurable_pairHamG' N k _ H lam a K₀ K z
  have hA (u) : Measurable (A u) := (measurable_pairHamG' N k _ H lam a K₀ K z).div hG
  have hGpos (x) : 0 < G x := pairHamG_pos N k (fun _ => zero_le_one)
    ⟨fun _ _ => true, one_pos⟩ H lam a K₀ K z x
  have hsum (x) : (∑ u ∈ parisiOverlapValues N, A u x) = 1 := by
    dsimp only [A]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, sum_pairHamG_constraintR]
    exact ENNReal.mul_inv_cancel (hGpos x).ne' ENNReal.ofReal_ne_top
  change (∑ u ∈ parisiOverlapValues N, cascadeTilt k ms μs G (A u)) = 1
  simp_rw [cascadeTilt_eq_lintegral_density k ms μs hG (hA _)]
  have hDA (u : ℝ) : Measurable (fun zs => cascadeTiltDensity k ms μs G zs * A u zs) :=
    (measurable_cascadeTiltDensity k ms μs hG).mul (hA u)
  rw [← lintegral_finsetSum _ (fun u _ => hDA u)]
  simp_rw [← Finset.mul_sum, hsum]
  rw [← cascadeTilt_eq_lintegral_density k ms μs hG measurable_const]
  exact cascadeTilt_one k ms μs hG hGpos hpos hle
    (lintegral_pairHamG_ne_top N k vs (fun _ => zero_le_one) H lam a K₀ K z)

theorem sum_parisiAuxTiltMass_toReal
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (r : Fin (k + 1)) (t : ℝ)
    (z : (EnergySpace N × (Fin N × Fin 2 → ℝ)) × (Fin N → ℝ)) :
    (∑ u ∈ parisiOverlapValues N, (parisiAuxTiltMass N ξ ms qs r t u z).toReal) = 1 := by
  have hfinite (u : ℝ) : parisiAuxTiltMass N ξ ms qs r t u z ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (pairHamConstrainedTiltMass_le_one _ _
      (constraintR_le_one N u) (halveBelow_pos hm.2.1 _)
      (halveBelow_le_one (fun i => (hm.2.2 i).le) _) z.1.1 0 _ _ _ z.1.2)
  rw [← ENNReal.toReal_sum (fun u _ => hfinite u)]
  change (∑ u ∈ parisiOverlapValues N, pairHamConstrainedTiltMass _ _ _ _ _ _ _ _ _).toReal = 1
  rw [sum_pairHamConstrainedTiltMass_constraintR (halveBelow r.val ms)
    (parisiAuxLevelVars ξ qs t) (halveBelow_pos hm.2.1 _)
    (halveBelow_le_one (fun i => (hm.2.2 i).le) _), ENNReal.toReal_one]

theorem integrable_parisiAuxTiltMass_toReal
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (t u : ℝ) :
    Integrable (fun z => (parisiAuxTiltMass N ξ ms qs r t u z).toReal)
      (parisiAuxDisorderFieldLaw N μh ξ qs t) := by
  apply Integrable.of_bound (measurable_pairHamConstrainedTiltMass_original ms
    (parisiAuxLevelVars ξ qs t) r.val (constraintR N u)).ennreal_toReal.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono ENNReal.one_ne_top (pairHamConstrainedTiltMass_le_one _ _
    (constraintR_le_one N u) (halveBelow_pos hm.2.1 _)
    (halveBelow_le_one (fun i => (hm.2.2 i).le) _) z.1.1 0 _ _ _ z.1.2)).trans_eq
    ENNReal.toReal_one

/-- Summing physical overlap atoms recovers the exact joint mass of
the meeting level, including the initial and terminal levels. -/
theorem sum_parisiBranchMeetingMass_eq_mass_increment
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (t : ℝ) :
    (∑ u ∈ parisiOverlapValues N, parisiBranchMeetingMass N μh ξ ms qs r t u) =
      mExt ms (r.val + 1) - mExt ms r.val := by
  simp_rw [parisiBranchMeetingMass_eq_integral_tilt μh ξ ms qs hm r t]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun u _ =>
    integrable_parisiAuxTiltMass_toReal μh ξ ms qs hm r t u)]
  simp_rw [sum_parisiAuxTiltMass_toReal ξ ms qs hm r t]
  simp

end SpinGlass
