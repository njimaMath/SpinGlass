import SpinGlass.Parisi.Concentration.PairGaussianCoefficients
import SpinGlass.FiniteGibbs.GaussianFieldProd

/-!
# Concrete standard Gaussian coordinates for disorder and root marks

Rows of the covariance square root provide the Gaussian representation.
The interaction block and the identity root block have their exact given
covariances, so the coefficient bounds require no representation hypothesis.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace SpinGlass

open FiniteGibbs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The row of the positive covariance square root, represented as a
vector in the standard Gaussian coordinate space. -/
noncomputable def gaussianSqrtCoeff (S : Matrix ι ι ℝ) (i : ι) : EuclideanSpace ℝ ι :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).adjoint (FiniteGibbs.std_basis i)

theorem inner_gaussianSqrtCoeff_apply (S : Matrix ι ι ℝ)
    (i : ι) (w : EuclideanSpace ℝ ι) :
    ⟪gaussianSqrtCoeff S i, w⟫ = Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) w i := by
  rw [gaussianSqrtCoeff, ContinuousLinearMap.adjoint_inner_left,
    FiniteGibbs.inner_std_basis_apply]

/-- The square-root coordinate map has the exact centered Gaussian law. -/
theorem map_gaussianSqrtCoeff (S : Matrix ι ι ℝ) :
    (stdGaussian (EuclideanSpace ℝ ι)).map
        (fun w => WithLp.toLp 2 (fun i => ⟪gaussianSqrtCoeff S i, w⟫)) =
      multivariateGaussian 0 S := by
  have he : (fun w => WithLp.toLp 2 (fun i => ⟪gaussianSqrtCoeff S i, w⟫)) =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) := by
    funext w
    ext i
    exact inner_gaussianSqrtCoeff_apply S i w
  rw [he]
  simp only [multivariateGaussian, zero_add]

/-- The coefficient Gram matrix is precisely the prescribed covariance,
including singular positive semidefinite matrices. -/
theorem inner_gaussianSqrtCoeff {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i j : ι) :
    ⟪gaussianSqrtCoeff S i, gaussianSqrtCoeff S j⟫ = S i j := by
  have hmap : (stdGaussian (EuclideanSpace ℝ ι)).map
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) = multivariateGaussian 0 S := by
    simp only [multivariateGaussian, zero_add]
  have hh := covarianceBilin_map (μ := stdGaussian (EuclideanSpace ℝ ι))
    IsGaussian.memLp_two_id (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))
    (FiniteGibbs.std_basis i) (FiniteGibbs.std_basis j)
  rw [hmap, covarianceBilin_multivariateGaussian hS,
    dotProduct_std_basis_mulVec, covarianceBilin_stdGaussian] at hh
  exact hh.symm

theorem norm_sq_gaussianSqrtCoeff {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i : ι) :
    ‖gaussianSqrtCoeff S i‖ ^ 2 = S i i := by
  rw [← real_inner_self_eq_norm_sq, inner_gaussianSqrtCoeff hS]

variable {N : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

/-- Independent interaction and standard root coordinates as one covariance
matrix. Root variances are absorbed into the physical root factors. -/
noncomputable def pairDisorderRootCovariance (S : Matrix (Config N) (Config N) ℝ) :
    Matrix (Config N ⊕ (Fin N × J)) (Config N ⊕ (Fin N × J)) ℝ :=
  Matrix.fromBlocks S 0 0 1

omit [Fintype J] in
theorem posSemidef_pairDisorderRootCovariance [Finite J] {S : Matrix (Config N) (Config N) ℝ}
    (hS : S.PosSemidef) : (pairDisorderRootCovariance (J := J) S).PosSemidef := by
  let : Fintype J := Fintype.ofFinite J
  let : Invertible (1 : Matrix (Fin N × J) (Fin N × J) ℝ) := invertibleOne
  have hh := (Matrix.PosDef.fromBlocks₂₂ S
    (0 : Matrix (Config N) (Fin N × J) ℝ) Matrix.PosDef.one).2
    (by simpa using hS)
  simpa only [pairDisorderRootCovariance, Matrix.conjTranspose_zero] using hh

/-- The root rows are genuinely orthonormal, including empty root index sets. -/
theorem orthonormal_pairDisorderRootCoeff {S : Matrix (Config N) (Config N) ℝ}
    (hS : S.PosSemidef) :
    Orthonormal ℝ (fun ij : Fin N × J =>
      gaussianSqrtCoeff (pairDisorderRootCovariance S) (Sum.inr ij)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_gaussianSqrtCoeff (posSemidef_pairDisorderRootCovariance hS)]
  simp [pairDisorderRootCovariance, Matrix.one_apply]

/-- The interaction rows retain their exact diagonal covariance. -/
theorem norm_sq_pairDisorderCoeff {S : Matrix (Config N) (Config N) ℝ}
    (hS : S.PosSemidef) (σ : Config N) :
    ‖gaussianSqrtCoeff (pairDisorderRootCovariance (J := J) S) (Sum.inl σ)‖ ^ 2 = S σ σ := by
  rw [norm_sq_gaussianSqrtCoeff (posSemidef_pairDisorderRootCovariance hS)]
  rfl

/-- The actual log tilted mass in the concrete joint Gaussian realization
of the interaction covariance and independent standard root marks. -/
noncomputable def pairGaussianLogTiltMass {k : ℕ}
    (S : Matrix (Config N) (Config N) ℝ) (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    (c : (Fin 2 → Config N) → ℝ) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (w : EuclideanSpace ℝ (Config N ⊕ (Fin N × J))) : ℝ :=
  pairHamLogTiltMass ms vs c
    (pairGaussianInteraction
      (fun σ => gaussianSqrtCoeff (pairDisorderRootCovariance S) (Sum.inl σ)) w)
    lam a K₀ K
    (fun ij => ⟪gaussianSqrtCoeff (pairDisorderRootCovariance S) (Sum.inr ij), w⟫)

/-- The Gaussian part of (14.121), with all coordinate and root-norm
conditions discharged from the finite covariance matrix. The remaining
constants are its diagonal bound and the physical root-factor row bound. -/
theorem hasSubgaussianMGF_pairGaussianLogTiltMass
    {S : Matrix (Config N) (Config N) ℝ} (hS : S.PosSemidef)
    {k : ℕ} (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    {D d : ℝ} (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hdiag : ∀ σ, S σ σ ≤ (N : ℝ) * D) (hK : ∀ l, ∑ j, K₀ l j ^ 2 ≤ d) :
    let F := pairGaussianLogTiltMass S ms vs c lam a K₀ K
    HasSubgaussianMGF
      (fun w => F w - ∫ w', F w' ∂stdGaussian (EuclideanSpace ℝ (Config N ⊕ (Fin N × J))))
      (32 * (N : ℝ) * (D + d)).toNNReal
      (stdGaussian (EuclideanSpace ℝ (Config N ⊕ (Fin N × J)))) := by
  exact hasSubgaussianMGF_pairHamLogTiltMass_of_diagonal_bound ms vs hc0 hc1 hcpos
    hsm hpos hlt _ _ (orthonormal_pairDisorderRootCoeff hS) lam a K₀ K hD hd
    (fun σ => by rw [norm_sq_pairDisorderCoeff hS]; exact hdiag σ) hK

end SpinGlass
