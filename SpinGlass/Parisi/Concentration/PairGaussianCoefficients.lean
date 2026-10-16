import SpinGlass.Parisi.Concentration.PairTiltGaussianConcentration

/-!
# Volume bounds for the Gaussian branch coefficients

Orthonormal root coordinates give the required square-root volume bound.
Only the interaction's diagonal covariance and the two root row norms
enter the concentration constant; the number of positive levels does not.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators RealInnerProductSpace

namespace SpinGlass

variable {N : ℕ} {J : Type*} [Fintype J]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The root field of one replica has variance $N\sum_j K_{0,lj}^2$
in orthonormal Gaussian coordinates, for every spin configuration. -/
theorem norm_sq_pairGaussianRootCoeff (B : Fin N × J → E) (hB : Orthonormal ℝ B)
    (K₀ : Fin 2 → J → ℝ) (l : Fin 2) (σ : Config N) :
    ‖∑ i, spin N σ i • ∑ j, K₀ l j • B (i, j)‖ ^ 2 =
      (N : ℝ) * ∑ j, K₀ l j ^ 2 := by
  classical
  have he : (∑ i, spin N σ i • ∑ j, K₀ l j • B (i, j)) =
      ∑ ij : Fin N × J, (spin N σ ij.1 * K₀ l ij.2) • B ij := by
    simp only [Fintype.sum_prod_type, Finset.smul_sum, smul_smul]
  rw [he, ← real_inner_self_eq_norm_sq]
  have hh := hB.inner_sum (fun ij => spin N σ ij.1 * K₀ l ij.2)
    (fun ij => spin N σ ij.1 * K₀ l ij.2) Finset.univ
  simp only [map_mul, conj_trivial, ← pow_two] at hh
  rw [hh, Fintype.sum_prod_type]
  have hs (i : Fin N) : spin N σ i ^ 2 = 1 := by
    simpa only [pow_two] using spin_mul_self N σ i
  simp only [mul_pow, hs, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- The actual branch coefficient has order $\sqrt N$ when the
interaction diagonal and root row variances are bounded. -/
theorem norm_pairGaussianBranchCoeff_le
    (A : Config N → E) (B : Fin N × J → E) (hB : Orthonormal ℝ B)
    (K₀ : Fin 2 → J → ℝ) {D d : ℝ} (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hA : ∀ σ, ‖A σ‖ ^ 2 ≤ (N : ℝ) * D)
    (hK : ∀ l, ∑ j, K₀ l j ^ 2 ≤ d) (σ : Fin 2 → Config N) :
    ‖pairGaussianBranchCoeff A B K₀ σ‖ ≤
      2 * (Real.sqrt ((N : ℝ) * D) + Real.sqrt ((N : ℝ) * d)) := by
  let R (l : Fin 2) := ∑ i, spin N (σ l) i • ∑ j, K₀ l j • B (i, j)
  have hAr (l : Fin 2) : ‖A (σ l)‖ ≤ Real.sqrt ((N : ℝ) * D) := by
    nlinarith [hA (σ l), Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hD),
      norm_nonneg (A (σ l)), Real.sqrt_nonneg ((N : ℝ) * D)]
  have hR (l : Fin 2) : ‖R l‖ ≤ Real.sqrt ((N : ℝ) * d) := by
    have hh : ‖R l‖ ^ 2 ≤ (N : ℝ) * d := by
      dsimp only [R]
      rw [norm_sq_pairGaussianRootCoeff B hB]
      exact mul_le_mul_of_nonneg_left (hK l) (Nat.cast_nonneg N)
    nlinarith [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hd), norm_nonneg (R l),
      Real.sqrt_nonneg ((N : ℝ) * d)]
  calc
    ‖pairGaussianBranchCoeff A B K₀ σ‖ = ‖(A (σ 0) + R 0) + (A (σ 1) + R 1)‖ := by
      congr 1
      simp only [pairGaussianBranchCoeff, Fin.sum_univ_two, R]
      abel
    _ ≤ ‖A (σ 0) + R 0‖ + ‖A (σ 1) + R 1‖ := norm_add_le _ _
    _ ≤ (Real.sqrt ((N : ℝ) * D) + Real.sqrt ((N : ℝ) * d)) +
        (Real.sqrt ((N : ℝ) * D) + Real.sqrt ((N : ℝ) * d)) :=
      add_le_add ((norm_add_le _ _).trans (add_le_add (hAr 0) (hR 0)))
        ((norm_add_le _ _).trans (add_le_add (hAr 1) (hR 1)))
    _ = 2 * (Real.sqrt ((N : ℝ) * D) + Real.sqrt ((N : ℝ) * d)) := by ring

/-- The Gaussian variance proxy is at most $32N(D+d)$ for the actual
logarithmic weighted mass. This includes the root variables and is uniform
in the external field, constraint, and cascade depth. -/
theorem hasSubgaussianMGF_pairHamLogTiltMass_of_diagonal_bound
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {k : ℕ} (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (A : Config N → E) (B : Fin N × J → E) (hB : Orthonormal ℝ B)
    (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    {D d : ℝ} (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hA : ∀ σ, ‖A σ‖ ^ 2 ≤ (N : ℝ) * D)
    (hK : ∀ l, ∑ j, K₀ l j ^ 2 ≤ d) :
    let F := fun w => pairHamLogTiltMass ms vs c (pairGaussianInteraction A w)
      lam a K₀ K (fun ij => ⟪B ij, w⟫)
    HasSubgaussianMGF (fun w => F w - ∫ w', F w' ∂stdGaussian E)
      (32 * (N : ℝ) * (D + d)).toNNReal (stdGaussian E) := by
  let C : ℝ≥0 := ⟨2 * (Real.sqrt ((N : ℝ) * D) + Real.sqrt ((N : ℝ) * d)), by positivity⟩
  have hC (σ : Fin 2 → Config N) : ‖pairGaussianBranchCoeff A B K₀ σ‖ ≤ C :=
    norm_pairGaussianBranchCoeff_le A B hB K₀ hD hd hA hK σ
  apply hasSubgaussianMGF_mono
    (hasSubgaussianMGF_pairHamLogTiltMass_gaussian ms vs hc0 hc1 hcpos hsm hpos hlt
      A B lam a K₀ K hC)
  have hNN : 0 ≤ 32 * (N : ℝ) * (D + d) := by positivity
  apply (NNReal.coe_le_coe).1
  rw [Real.coe_toNNReal _ hNN]
  change (2 * (2 * (Real.sqrt ((N : ℝ) * D) + Real.sqrt ((N : ℝ) * d)))) ^ 2 ≤ _
  have hsD := Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hD)
  have hsd := Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hd)
  nlinarith [sq_nonneg (Real.sqrt ((N : ℝ) * D) - Real.sqrt ((N : ℝ) * d))]

end SpinGlass
