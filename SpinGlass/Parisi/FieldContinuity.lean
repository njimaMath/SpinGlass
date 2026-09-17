import SpinGlass.Parisi.ParisiMin

/-!
# Uniform continuity in a constant external field

The constants in these estimates do not depend on the volume or the number
of recursion levels. They supply the field-to-zero reduction of Theorem 14.5.1.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SpinGlass

private theorem free_energy_density_le_add_of_pointwise_bound
    {N : ℕ} (hN : 0 < N) (H₁ H₂ : EnergySpace N) (c : ℝ)
    (hb : ∀ σ, -H₂ σ ≤ -H₁ σ + (N : ℝ) * c) :
    free_energy_density N H₂ ≤ free_energy_density N H₁ + c := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hZ : Z N H₂ ≤ Real.exp ((N : ℝ) * c) * Z N H₁ := by
    calc
      _ ≤ ∑ σ : Config N, Real.exp (-H₁ σ + (N : ℝ) * c) :=
        Finset.sum_le_sum fun σ _ => Real.exp_le_exp.2 (hb σ)
      _ = Real.exp ((N : ℝ) * c) * Z N H₁ := by
        simp only [Real.exp_add, Finset.mul_sum, Z]
        apply Finset.sum_congr rfl
        intro σ _
        ring
  have hlog := Real.log_le_log (Z_pos N H₂) hZ
  rw [Real.log_mul (Real.exp_ne_zero _) (Z_pos N H₁).ne', Real.log_exp] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 1 / (N : ℝ))
  have hcalc : (1 / (N : ℝ)) * ((N : ℝ) * c + Real.log (Z N H₁)) =
      (1 / (N : ℝ)) * Real.log (Z N H₁) + c := by
    field_simp
    ring
  rw [hcalc] at hm
  exact hm

/-- A constant-field perturbation changes the finite-volume value by at most
the magnitude of the perturbation, uniformly in positive volumes. -/
theorem abs_mixedPSpinFreeEnergy_sub_field_le
    {N : ℕ} (hN : 0 < N) (ξ : ℝ → ℝ) (a b : ℝ) :
    |mixedPSpinFreeEnergy N ξ a - mixedPSpinFreeEnergy N ξ b| ≤ |a - b| := by
  have hpoint (H : EnergySpace N) (a b : ℝ) :
      free_energy_density N (H + H_field N a) ≤
        free_energy_density N (H + H_field N b) + |a - b| := by
    apply free_energy_density_le_add_of_pointwise_bound hN
    intro σ
    have hmag := mul_le_mul_of_nonneg_left (abs_magnetization_le N σ) (abs_nonneg (a - b))
    have heq : -(H + H_field N a) σ = -(H + H_field N b) σ -
        (a - b) * magnetization N σ := by
      change -(H σ + a * magnetization N σ) =
        -(H σ + b * magnetization N σ) - (a - b) * magnetization N σ
      ring
    rw [heq]
    have hab : -((a - b) * magnetization N σ) ≤ (N : ℝ) * |a - b| := by
      calc
        _ ≤ |(a - b) * magnetization N σ| := neg_le_abs _
        _ ≤ (N : ℝ) * |a - b| := by simpa only [abs_mul, mul_comm] using hmag
    linarith
  have hmean (a b : ℝ) : mixedPSpinFreeEnergy N ξ a ≤
      mixedPSpinFreeEnergy N ξ b + |a - b| := by
    have h := integral_mono
      (integrable_free_energy_density_shift (overlapCovMatrix N ξ) a)
      ((integrable_free_energy_density_shift (overlapCovMatrix N ξ) b).add
        (integrable_const |a - b|)) (fun H => hpoint H a b)
    change (∫ H, free_energy_density N (H + H_field N a)
      ∂gaussField N (overlapCovMatrix N ξ)) ≤
      ∫ H, free_energy_density N (H + H_field N b) + |a - b|
        ∂gaussField N (overlapCovMatrix N ξ) at h
    rw [integral_add (integrable_free_energy_density_shift (overlapCovMatrix N ξ) b)
      (integrable_const |a - b|), integral_const, probReal_univ, one_smul] at h
    exact h
  apply abs_le.2
  constructor
  · have h := hmean b a
    rw [abs_sub_comm b a] at h
    linarith
  · linarith [hmean a b]

/-- The deterministic-field functional is one-Lipschitz in the field for
positive admissible masses. -/
theorem abs_parisiFunctional_sub_field_le
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (a b : ℝ) :
    |parisiFunctional ξ a ms qs - parisiFunctional ξ b ms qs| ≤ |a - b| := by
  let vs : Fin k → ℝ≥0 := fun p => parisiVar ξ qs (p.val + 1)
  have hlip (x y : ℝ) : |logCoshRec k ms vs y - logCoshRec k ms vs x| ≤ |y - x| := by
    rw [logCoshRec_eq_coleHopfIterate_terminal_zero ms vs hpos y,
      logCoshRec_eq_coleHopfIterate_terminal_zero ms vs hpos x]
    simpa only [one_mul] using abs_coleHopfIterate_sub_le k ms vs (L := 1)
      (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0))
      (fun x y => by simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0 x y) x y
  have hi (h : ℝ) := integrable_logCoshRec_add k ms vs hpos hle h (parisiVar ξ qs 0)
  have hbound : |(∫ z, logCoshRec k ms vs (a + z) ∂gaussianReal 0 (parisiVar ξ qs 0)) -
      (∫ z, logCoshRec k ms vs (b + z) ∂gaussianReal 0 (parisiVar ξ qs 0))| ≤ |a - b| := by
    rw [← integral_sub (hi a) (hi b)]
    calc
      _ ≤ ∫ z, |logCoshRec k ms vs (a + z) - logCoshRec k ms vs (b + z)|
          ∂gaussianReal 0 (parisiVar ξ qs 0) := abs_integral_le_integral_abs
      _ ≤ ∫ _z, |a - b| ∂gaussianReal 0 (parisiVar ξ qs 0) := by
        apply integral_mono ((hi a).sub (hi b)).abs (integrable_const |a - b|)
        intro z
        change |logCoshRec k ms vs (a + z) - logCoshRec k ms vs (b + z)| ≤ |a - b|
        simpa only [add_sub_add_right_eq_sub] using hlip (b + z) (a + z)
      _ = |a - b| := by simp only [integral_const, probReal_univ, one_smul]
  unfold parisiFunctional
  rw [parisiX₀_logCosh_eq k ξ a ms qs hpos hle,
    parisiX₀_logCosh_eq k ξ b ms qs hpos hle]
  convert hbound using 1
  congr 1
  ring

/-- The infimum retains the field-continuity constant of every admissible value. -/
theorem abs_parisiInf_sub_field_le {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) (a b : ℝ) :
    |parisiInf ξ a - parisiInf ξ b| ≤ |a - b| := by
  have hbdd (h : ℝ) : BddBelow (parisiSet ξ h) := by
    simpa only [randomFieldParisiSet_dirac] using
      bddBelow_randomFieldParisiSet_of_talagrand (Measure.dirac h) hξ
  have hone (a b : ℝ) : parisiInf ξ a ≤ parisiInf ξ b + |a - b| := by
    have h : parisiInf ξ a - |a - b| ≤ sInf (parisiSet ξ b) := by
      apply le_csInf (parisiSet_nonempty ξ b)
      rintro y ⟨k, ms, qs, hsm, hpos, hlt, hmono, hq0, hq1, rfl⟩
      have ha := parisiInf_le ξ a (hbdd a) hsm hpos hlt hmono hq0 hq1
      have hab := (abs_le.1 (abs_parisiFunctional_sub_field_le ξ ms qs hpos
        (fun i => (hlt i).le) a b)).2
      linarith
    change parisiInf ξ a - |a - b| ≤ parisiInf ξ b at h
    linarith
  apply abs_le.2
  constructor
  · have h := hone b a
    rw [abs_sub_comm b a] at h
    linarith
  · linarith [hone a b]

end SpinGlass
