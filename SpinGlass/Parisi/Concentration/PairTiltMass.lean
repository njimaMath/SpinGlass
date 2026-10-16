import SpinGlass.Parisi.Concentration.CascadeTiltContinuity
import SpinGlass.Parisi.Coupled.CoupledFieldPressure

/-!
# The constrained two-replica tilted mass

The terminal factor is the actual constrained branch partition function
divided by the unconstrained one. Its cascade tilted average is the
quantity in (14.117)-(14.121). The bounds below discharge the Gaussian
integrability and positivity conditions for the physical branch functions.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N k : ℕ} {J : Type*} [Fintype J]

/-- Monotonicity in the physical constraint, before any averaging. -/
theorem pairHamG_mono_constraint {c d : (Fin 2 → Config N) → ℝ} (hcd : ∀ σ, c σ ≤ d σ)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) :
    pairHamG N k c H lam a K₀ K z₀ x ≤ pairHamG N k d H lam a K₀ K z₀ x := by
  unfold pairHamG pairBranchZX
  exact ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun σ _ =>
    mul_le_mul_of_nonneg_right (hcd σ) (Real.exp_nonneg _))

/-- The actual tilted expectation of the constrained terminal ratio,
with every positive Gaussian cascade level retained. -/
noncomputable def pairHamConstrainedTiltMass (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) : ℝ≥0∞ :=
  cascadeTilt k ms (siteGaussianMarks (Fin N × J) k vs)
    (pairHamG N k (fun _ => 1) H lam a K₀ K z₀)
    (fun x => pairHamG N k c H lam a K₀ K z₀ x /
      pairHamG N k (fun _ => 1) H lam a K₀ K z₀ x)

/-- Its logarithm is the random variable to which concentration is
applied. Positivity for a nonempty constraint is proved below. -/
noncomputable def pairHamLogTiltMass (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) : ℝ :=
  Real.log (pairHamConstrainedTiltMass ms vs c H lam a K₀ K z₀).toReal

theorem pairHamConstrainedTiltMass_le_one (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc1 : ∀ σ, c σ ≤ 1)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) :
    pairHamConstrainedTiltMass ms vs c H lam a K₀ K z₀ ≤ 1 :=
  cascadeTilt_div_le_one ms _
    (measurable_pairHamG' N k _ H lam a K₀ K z₀)
    (fun x => pairHamG_pos N k (fun _ => zero_le_one) ⟨fun _ _ => true, one_pos⟩
      H lam a K₀ K z₀ x)
    (fun _ => ENNReal.ofReal_ne_top)
    (pairHamG_mono_constraint hc1 H lam a K₀ K z₀) hpos hle
    (lintegral_pairHamG_ne_top N k vs (fun _ => zero_le_one) H lam a K₀ K z₀)

theorem pairHamConstrainedTiltMass_pos (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hcpos : ∃ σ, 0 < c σ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) :
    0 < pairHamConstrainedTiltMass ms vs c H lam a K₀ K z₀ :=
  cascadeTilt_pos_of_pos ms _ (measurable_pairHamG' N k _ H lam a K₀ K z₀)
    ((measurable_pairHamG' N k c H lam a K₀ K z₀).div
      (measurable_pairHamG' N k _ H lam a K₀ K z₀))
    (fun x => pairHamG_pos N k (fun _ => zero_le_one) ⟨fun _ _ => true, one_pos⟩
      H lam a K₀ K z₀ x)
    (fun x => ENNReal.div_pos (pairHamG_pos N k hc0 hcpos H lam a K₀ K z₀ x).ne'
      ENNReal.ofReal_ne_top) hpos hle
    (lintegral_pairHamG_ne_top N k vs (fun _ => zero_le_one) H lam a K₀ K z₀)

/-- The concrete branch functions satisfy every hypothesis of the
recursive logarithmic comparison (14.120), for all Gaussian variances. -/
theorem pairHamLogTiltMass_le_pressure_gap (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hmono : Monotone ms)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hblower : ∀ i, b ≤ ms i) :
    pairHamLogTiltMass ms vs c H lam a K₀ K z₀ ≤
      b * (Real.log (cascadeRec k ms (siteGaussianMarks (Fin N × J) k vs)
        (pairHamG N k c H lam a K₀ K z₀)).toReal -
          Real.log (cascadeRec k ms (siteGaussianMarks (Fin N × J) k vs)
            (pairHamG N k (fun _ => 1) H lam a K₀ K z₀)).toReal) :=
  log_cascadeTilt_div_le_cascadeRec_gap ms _
    (measurable_pairHamG' N k _ H lam a K₀ K z₀)
    (measurable_pairHamG' N k c H lam a K₀ K z₀)
    (fun x => pairHamG_pos N k (fun _ => zero_le_one) ⟨fun _ _ => true, one_pos⟩
      H lam a K₀ K z₀ x)
    (fun x => pairHamG_pos N k hc0 hcpos H lam a K₀ K z₀ x)
    (fun _ => ENNReal.ofReal_ne_top) (pairHamG_mono_constraint hc1 H lam a K₀ K z₀)
    hmono hpos hle
    (lintegral_pairHamG_ne_top N k vs (fun _ => zero_le_one) H lam a K₀ K z₀) hb hb1 hblower

/-- The actual logarithmic tilted mass has a field perturbation bound
uniform in the number of levels, all disorder, and all Gaussian marks. -/
theorem abs_pairHamLogTiltMass_sub_field_le (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (H : EnergySpace N) (lam : ℝ) (a b : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) :
    |pairHamLogTiltMass ms vs c H lam a K₀ K z₀ -
      pairHamLogTiltMass ms vs c H lam b K₀ K z₀| ≤ 2 * replicaSiteFieldDistance a b := by
  have hupper (a b : Fin N × Fin 2 → ℝ) :
      pairHamLogTiltMass ms vs c H lam a K₀ K z₀ -
        pairHamLogTiltMass ms vs c H lam b K₀ K z₀ ≤ 2 * replicaSiteFieldDistance a b := by
    apply log_cascadeTilt_div_sub_le_of_exp_mul_le ms _
      (measurable_pairHamG' N k _ H lam a K₀ K z₀)
      (measurable_pairHamG' N k _ H lam b K₀ K z₀)
      (measurable_pairHamG' N k c H lam a K₀ K z₀)
      (measurable_pairHamG' N k c H lam b K₀ K z₀)
      (fun x => pairHamG_pos N k (fun _ => zero_le_one) ⟨fun _ _ => true, one_pos⟩
        H lam a K₀ K z₀ x)
      (fun x => pairHamG_pos N k (fun _ => zero_le_one) ⟨fun _ _ => true, one_pos⟩
        H lam b K₀ K z₀ x)
      (fun x => pairHamG_pos N k hc0 hcpos H lam a K₀ K z₀ x)
      (fun x => pairHamG_pos N k hc0 hcpos H lam b K₀ K z₀ x)
      (fun _ => ENNReal.ofReal_ne_top) (fun _ => ENNReal.ofReal_ne_top)
      (pairHamG_mono_constraint hc1 H lam a K₀ K z₀)
      (pairHamG_mono_constraint hc1 H lam b K₀ K z₀)
      (lintegral_pairHamG_ne_top N k vs (fun _ => zero_le_one) H lam a K₀ K z₀)
      (lintegral_pairHamG_ne_top N k vs (fun _ => zero_le_one) H lam b K₀ K z₀)
      hsm hpos hlt (replicaSiteFieldDistance a b)
      (pairHamG_field_le_exp_mul hc0 H lam a b K₀ K z₀)
    rw [replicaSiteFieldDistance_comm a b]
    exact pairHamG_field_le_exp_mul (fun _ => zero_le_one) H lam b a K₀ K z₀
  exact abs_le.2 ⟨by
    have hh := hupper b a
    rw [replicaSiteFieldDistance_comm b a] at hh
    linarith, hupper a b⟩

/-- In particular the logarithmic tilted mass is continuous and
measurable in the realized replica field vector. -/
theorem lipschitzWith_pairHamLogTiltMass_field (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (H : EnergySpace N) (lam : ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) :
    LipschitzWith (4 * (N : ℝ≥0))
      (fun a : Fin N × Fin 2 → ℝ => pairHamLogTiltMass ms vs c H lam a K₀ K z₀) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hcoord (p : Fin N × Fin 2) : |a p - b p| ≤ dist a b := by
    simpa only [Real.dist_eq] using dist_le_pi_dist a b p
  calc
    _ ≤ 2 * replicaSiteFieldDistance a b :=
      abs_pairHamLogTiltMass_sub_field_le ms vs hc0 hc1 hcpos hsm hpos hlt H lam a b K₀ K z₀
    _ ≤ 2 * (∑ _l : Fin 2, ∑ _i : Fin N, dist a b) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun i _ => hcoord (i, l)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast]
      ring

end SpinGlass
