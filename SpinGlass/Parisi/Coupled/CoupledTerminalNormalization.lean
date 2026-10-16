import SpinGlass.Parisi.Coupled.CoupledAuxiliaryTransport

/-!
# Integrating the terminal mass-one Gaussian level

The mass-one operation is an ordinary expectation. The terminal independent
two-replica Gaussian field contributes exp(N v), for terminal variance v.
This is the constant removed in Talagrand's (14.312).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- A terminal mass-one level is exactly its conditional expectation,
for an arbitrary measurable mark space and arbitrary preceding masses. -/
theorem cascadeRec_snoc_one_integral {T : Type*} [MeasurableSpace T] (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T) (ν : Measure T)
      (G : (Fin (k + 1) → T) → ℝ≥0∞),
      cascadeRec (k + 1) (Fin.snoc ms 1) (Fin.snoc μs ν) G =
        cascadeRec k ms μs (fun xs => ∫⁻ z, G (Fin.snoc xs z) ∂ν) := by
  induction k with
  | zero =>
    intro ms μs ν G
    simp only [cascadeRec_succ, cascadeRec_zero]
    change (∫⁻ z, G (Fin.cons z Fin.elim0) ^
      (Fin.snoc (α := fun _ => ℝ) ms 1 (Fin.last 0))
      ∂Fin.snoc (α := fun _ => Measure T) μs ν (Fin.last 0)) ^
        (1 / Fin.snoc (α := fun _ => ℝ) ms 1 (Fin.last 0)) = _
    simp only [Fin.snoc_last, one_div_one, ENNReal.rpow_one]
    apply lintegral_congr
    intro z
    congr 1
    funext i
    have hi : i = (0 : Fin 1) := Fin.ext (by omega)
    subst i
    rfl
  | succ k ih =>
    intro ms μs ν G
    rw [cascadeRec_succ, cascadeRec_succ, fin_tail_snoc, fin_tail_snoc]
    have h0m : (Fin.snoc ms (1 : ℝ) : Fin (k + 2) → ℝ) 0 = ms 0 := by
      rw [show (0 : Fin (k + 2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
    have h0μ : (Fin.snoc μs ν : Fin (k + 2) → Measure T) 0 = μs 0 := by
      rw [show (0 : Fin (k + 2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
    rw [h0m, h0μ]
    congr 1
    apply lintegral_congr
    intro z
    rw [ih]
    congr 2
    funext xs
    apply lintegral_congr
    intro w
    rw [Fin.cons_snoc_eq_snoc_cons]

/-- The covariance identity for independent terminal replicas gives
the same exponential moment for every spin configuration. -/
theorem terminal_pair_spin_variance {N : ℕ} {J : Type*} [Fintype J]
    (v : ℝ≥0) (K : Fin 2 → J → ℝ)
    (hK : ∀ l l', gram K l l' = if l = l' then 1 else 0) (σ : Fin 2 → Config N) :
    (∑ s : Fin N × J, (v : ℝ) * (-(∑ l : Fin 2, isingSpin (σ l s.1) * K l s.2)) ^ 2 / 2) =
      (N : ℝ) * v := by
  have hlocal (i : Fin N) :
      (∑ j : J, (v : ℝ) * (-(∑ l : Fin 2, isingSpin (σ l i) * K l j)) ^ 2 / 2) = (v : ℝ) := by
    let a := isingSpin (σ 0 i)
    let b := isingSpin (σ 1 i)
    have he : (∑ j : J, (v : ℝ) * (-(a * K 0 j + b * K 1 j)) ^ 2 / 2) =
        (v : ℝ) / 2 * (a ^ 2 * gram K 0 0 + 2 * a * b * gram K 0 1 + b ^ 2 * gram K 1 1) := by
      simp only [gram, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp only [Fin.sum_univ_two]
    change (∑ j : J, (v : ℝ) * (-(a * K 0 j + b * K 1 j)) ^ 2 / 2) = (v : ℝ)
    rw [he, hK 0 0, hK 0 1, hK 1 1]
    have ha : a ^ 2 = 1 := by simpa only [pow_two] using isingSpin_mul_self (σ 0 i)
    have hb : b ^ 2 = 1 := by simpa only [pow_two] using isingSpin_mul_self (σ 1 i)
    norm_num [ha, hb]
  rw [Fintype.sum_prod_type]
  simp_rw [hlocal]
  simp

/-- The last Gaussian mark averages the actual constrained partition
function by exp(N v), independently of all earlier marks and fields. -/
theorem lintegral_pairHamG_snoc_terminal {N k : ℕ} {J : Type*} [Fintype J]
    {c : (Fin 2 → Config N) → ℝ} (hc : ∀ σ, 0 ≤ c σ)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (KT : Fin 2 → J → ℝ)
    (hKT : ∀ l l', gram KT l l' = if l = l' then 1 else 0)
    (z₀ : Fin N × J → ℝ) (xs : Fin k → Fin N × J → ℝ) (v : ℝ≥0) :
    (∫⁻ z, pairHamG N (k + 1) c H lam a K₀ (Fin.snoc K KT) z₀ (Fin.snoc xs z)
      ∂Measure.pi (fun _ : Fin N × J => gaussianReal 0 v)) =
      ENNReal.ofReal (Real.exp ((N : ℝ) * v)) * pairHamG N k c H lam a K₀ K z₀ xs := by
  classical
  have hsplit (σ : Fin 2 → Config N) (z : Fin N × J → ℝ) :
      pairBranchA N H lam a K₀ z₀ σ +
          ∑ p : Fin (k + 1), ∑ s : Fin N × J,
            pairBranchB N (k + 1) (Fin.snoc K KT) σ p s *
              (Fin.snoc (α := fun _ => Fin N × J → ℝ) xs z p) s =
        -pairBranchHamX N k H lam a K₀ K z₀ xs σ +
          ∑ s, (-(∑ l, isingSpin (σ l s.1) * KT l s.2)) * z s := by
    rw [neg_pairBranchHamX_eq, Fin.sum_univ_castSucc]
    simp only [pairBranchB, Fin.snoc_castSucc, Fin.snoc_last]
    ring
  simp_rw [pairHamG_eq_sum N (k + 1) hc, hsplit, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_finsetSum _ (fun σ _ => by fun_prop)]
  simp_rw [← mul_assoc]
  rw [pairHamG_eq_sum N k hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [lintegral_const_mul _ (by fun_prop), lintegral_ofReal_exp_sum_mul_pi_gaussianReal,
    terminal_pair_spin_variance v KT hKT σ, neg_pairBranchHamX_eq]
  ring

/-- The full terminal Gaussian normalization passes through every
earlier positive-mass cascade level. -/
theorem cascadeRec_pairHamG_snoc_terminal_eq {N k : ℕ} {J : Type*} [Fintype J]
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    {c : (Fin 2 → Config N) → ℝ} (hc : ∀ σ, 0 ≤ c σ)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (KT : Fin 2 → J → ℝ)
    (hKT : ∀ l l', gram KT l l' = if l = l' then 1 else 0)
    (z₀ : Fin N × J → ℝ) (v : ℝ≥0) :
    cascadeRec (k + 1) (Fin.snoc ms 1)
        (siteGaussianMarks (Fin N × J) (k + 1) (Fin.snoc vs v))
        (pairHamG N (k + 1) c H lam a K₀ (Fin.snoc K KT) z₀) =
      ENNReal.ofReal (Real.exp ((N : ℝ) * v)) *
        cascadeRec k ms (siteGaussianMarks (Fin N × J) k vs)
          (pairHamG N k c H lam a K₀ K z₀) := by
  have hμ : siteGaussianMarks (Fin N × J) (k + 1) (Fin.snoc vs v) =
      Fin.snoc (siteGaussianMarks (Fin N × J) k vs)
        (Measure.pi (fun _ : Fin N × J => gaussianReal 0 v)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [siteGaussianMarks, Fin.snoc_last]
    · simp only [siteGaussianMarks, Fin.snoc_castSucc]
  rw [hμ, cascadeRec_snoc_one_integral]
  simp_rw [lintegral_pairHamG_snoc_terminal hc H lam a K₀ K KT hKT _ _ v]
  rw [cascadeRec_const_mul k ms _ (measurable_pairHamG' N k c H lam a K₀ K z₀) hpos]

/-- The terminal mass-one field adds N v to the logarithmic cascade
partition function, with positivity and finiteness proved for its constraint. -/
theorem log_cascadeRec_pairHamG_snoc_terminal_eq {N k : ℕ} {J : Type*} [Fintype J]
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    {c : (Fin 2 → Config N) → ℝ} (hc : ∀ σ, 0 ≤ c σ) (hcpos : ∃ σ, 0 < c σ)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (KT : Fin 2 → J → ℝ)
    (hKT : ∀ l l', gram KT l l' = if l = l' then 1 else 0)
    (z₀ : Fin N × J → ℝ) (v : ℝ≥0) :
    Real.log (cascadeRec (k + 1) (Fin.snoc ms 1)
        (siteGaussianMarks (Fin N × J) (k + 1) (Fin.snoc vs v))
        (pairHamG N (k + 1) c H lam a K₀ (Fin.snoc K KT) z₀)).toReal =
      (N : ℝ) * v + Real.log (cascadeRec k ms (siteGaussianMarks (Fin N × J) k vs)
        (pairHamG N k c H lam a K₀ K z₀)).toReal := by
  have hfin := cascadeRec_pairHamG_ne_top N k ms vs hpos hle hc H lam a K₀ K z₀
  have hp := cascadeRec_pos k ms (siteGaussianMarks (Fin N × J) k vs)
    (measurable_pairHamG' N k c H lam a K₀ K z₀)
    (fun xs => pairHamG_pos N k hc hcpos H lam a K₀ K z₀ xs) hpos
  rw [cascadeRec_pairHamG_snoc_terminal_eq ms vs hpos hc H lam a K₀ K KT hKT z₀ v,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.log_mul (Real.exp_pos _).ne' (ENNReal.toReal_pos hp.ne' hfin).ne', Real.log_exp]

end SpinGlass
