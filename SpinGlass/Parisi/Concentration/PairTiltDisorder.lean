import SpinGlass.Parisi.Concentration.PairTiltMass

/-!
# Disorder perturbations of the logarithmic constrained mass

Uniform branch Hamiltonian perturbations control the actual logarithmic
tilted mass. This deterministic estimate is the input for Gaussian
concentration after representing the disorder and root marks by coordinates.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N k : ℕ} {J : Type*} [Fintype J]

/-- A uniform branch energy perturbation controls every constrained
partition function, including the unconstrained denominator. -/
theorem pairHamG_le_exp_mul_of_hamiltonian_bound
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ)
    (H H' : EnergySpace N) (lam : ℝ) (a a' : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z₀ z₀' : Fin N × J → ℝ) {C : ℝ}
    (hbound : ∀ x σ, |pairBranchHamX N k H lam a K₀ K z₀ x σ -
      pairBranchHamX N k H' lam a' K₀ K z₀' x σ| ≤ C)
    (x : Fin k → Fin N × J → ℝ) :
    pairHamG N k c H lam a K₀ K z₀ x ≤
      ENNReal.ofReal (Real.exp C) * pairHamG N k c H' lam a' K₀ K z₀' x := by
  unfold pairHamG
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg C)]
  apply ENNReal.ofReal_le_ofReal
  unfold pairBranchZX
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  have he : Real.exp (-pairBranchHamX N k H lam a K₀ K z₀ x σ) ≤
      Real.exp C * Real.exp (-pairBranchHamX N k H' lam a' K₀ K z₀' x σ) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith [(abs_le.1 (hbound x σ)).1]
  have hh := mul_le_mul_of_nonneg_left he (hc0 σ)
  nlinarith only [hh]

/-- A perturbation bound on the actual branch Hamiltonians gives a
level-independent bound on the logarithmic weighted product. Both the
interaction disorder and root marks may vary in this comparison. -/
theorem abs_pairHamLogTiltMass_sub_le_of_hamiltonian_bound
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (H H' : EnergySpace N) (lam : ℝ) (a a' : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z₀ z₀' : Fin N × J → ℝ) {C : ℝ}
    (hbound : ∀ x σ, |pairBranchHamX N k H lam a K₀ K z₀ x σ -
      pairBranchHamX N k H' lam a' K₀ K z₀' x σ| ≤ C) :
    |pairHamLogTiltMass ms vs c H lam a K₀ K z₀ -
      pairHamLogTiltMass ms vs c H' lam a' K₀ K z₀'| ≤ 2 * C := by
  have hupper (H H' : EnergySpace N) (a a' : Fin N × Fin 2 → ℝ)
      (z₀ z₀' : Fin N × J → ℝ)
      (hb : ∀ x σ, |pairBranchHamX N k H lam a K₀ K z₀ x σ -
        pairBranchHamX N k H' lam a' K₀ K z₀' x σ| ≤ C) :
      pairHamLogTiltMass ms vs c H lam a K₀ K z₀ -
        pairHamLogTiltMass ms vs c H' lam a' K₀ K z₀' ≤ 2 * C := by
    apply log_cascadeTilt_div_sub_le_of_exp_mul_le ms _
      (measurable_pairHamG' N k _ H lam a K₀ K z₀)
      (measurable_pairHamG' N k _ H' lam a' K₀ K z₀')
      (measurable_pairHamG' N k c H lam a K₀ K z₀)
      (measurable_pairHamG' N k c H' lam a' K₀ K z₀')
      (fun x => pairHamG_pos N k (fun _ => zero_le_one) ⟨fun _ _ => true, one_pos⟩
        H lam a K₀ K z₀ x)
      (fun x => pairHamG_pos N k (fun _ => zero_le_one) ⟨fun _ _ => true, one_pos⟩
        H' lam a' K₀ K z₀' x)
      (fun x => pairHamG_pos N k hc0 hcpos H lam a K₀ K z₀ x)
      (fun x => pairHamG_pos N k hc0 hcpos H' lam a' K₀ K z₀' x)
      (fun _ => ENNReal.ofReal_ne_top) (fun _ => ENNReal.ofReal_ne_top)
      (pairHamG_mono_constraint hc1 H lam a K₀ K z₀)
      (pairHamG_mono_constraint hc1 H' lam a' K₀ K z₀')
      (lintegral_pairHamG_ne_top N k vs (fun _ => zero_le_one) H lam a K₀ K z₀)
      (lintegral_pairHamG_ne_top N k vs (fun _ => zero_le_one) H' lam a' K₀ K z₀')
      hsm hpos hlt C (pairHamG_le_exp_mul_of_hamiltonian_bound hc0 H H' lam a a' K₀ K z₀ z₀' hb)
    exact pairHamG_le_exp_mul_of_hamiltonian_bound (fun _ => zero_le_one)
      H' H lam a' a K₀ K z₀' z₀ (fun x σ => by simpa only [abs_sub_comm] using hb x σ)
  have hreverse := hupper H' H a' a z₀' z₀
    (fun x σ => by simpa only [abs_sub_comm] using hbound x σ)
  exact abs_le.2 ⟨by linarith only [hreverse], hupper H H' a a' z₀ z₀' hbound⟩

/-- A uniform perturbation of the single-replica interaction energy
changes the logarithmic constrained tilted mass by at most four times
that perturbation, independently of volume and cascade depth. -/
theorem abs_pairHamLogTiltMass_sub_disorder_le (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (H H' : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ)
    {D : ℝ} (hD : ∀ σ, |H σ - H' σ| ≤ D) :
    |pairHamLogTiltMass ms vs c H lam a K₀ K z₀ -
      pairHamLogTiltMass ms vs c H' lam a K₀ K z₀| ≤ 4 * D := by
  have hbound (x : Fin k → Fin N × J → ℝ) (σ : Fin 2 → Config N) :
      |pairBranchHamX N k H lam a K₀ K z₀ x σ -
        pairBranchHamX N k H' lam a K₀ K z₀ x σ| ≤ 2 * D := by
    have he : pairBranchHamX N k H lam a K₀ K z₀ x σ -
        pairBranchHamX N k H' lam a K₀ K z₀ x σ =
          (H (σ 0) - H' (σ 0)) + (H (σ 1) - H' (σ 1)) := by
      unfold pairBranchHamX
      ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith [hD (σ 0), hD (σ 1)])
  have hh := abs_pairHamLogTiltMass_sub_le_of_hamiltonian_bound ms vs hc0 hc1 hcpos
    hsm hpos hlt H H' lam a a K₀ K z₀ z₀ hbound
  linarith only [hh]

end SpinGlass
