import SpinGlass.Parisi.Concentration.GaussianCoordinates
import Common.Mathlib.Probability.Distributions.Gaussian.MultivariateUniqueness
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Exact joint law of the Gaussian concentration coordinates

The square-root representation has the original interaction covariance
and independent standard Gaussian root marks. This identifies the
concentrated observable with the physical product-law observable.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators RealInnerProductSpace

namespace SpinGlass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite family of Gaussian coefficient vectors as a continuous linear map. -/
noncomputable def gaussianCoeffCLM (A : ι → E) : E →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => innerSL ℝ (A i)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [DecidableEq ι] in
theorem gaussianCoeffCLM_apply (A : ι → E) (w : E) (i : ι) :
    gaussianCoeffCLM A w i = ⟪A i, w⟫ := rfl

omit [DecidableEq ι] [MeasurableSpace E] [BorelSpace E] in
theorem adjoint_gaussianCoeffCLM_std_basis (A : ι → E) (i : ι) :
    (gaussianCoeffCLM A).adjoint (FiniteGibbs.std_basis i) = A i := by
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left, FiniteGibbs.inner_std_basis_apply,
    gaussianCoeffCLM_apply]

/-- The law of linear Gaussian coordinates is determined by their Gram matrix. -/
theorem map_stdGaussian_gaussianCoeffCLM (A : ι → E) (S : Matrix ι ι ℝ)
    (hA : ∀ i j, ⟪A i, A j⟫ = S i j) :
    (stdGaussian E).map (gaussianCoeffCLM A) = multivariateGaussian 0 S := by
  apply IsGaussian.eq_multivariateGaussian_of_covarianceBilin
  · rw [(gaussianCoeffCLM A).integral_id_map IsGaussian.integrable_id,
      integral_id_stdGaussian, map_zero]
  · intro i j
    rw [← FiniteGibbs.std_basis_eq_single i, ← FiniteGibbs.std_basis_eq_single j]
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      adjoint_gaussianCoeffCLM_std_basis, adjoint_gaussianCoeffCLM_std_basis,
      covarianceBilin_stdGaussian]
    exact hA i j

omit [Fintype ι] [DecidableEq ι] in
/-- Orthogonal blocks of the jointly Gaussian coordinates are independent. -/
theorem indepFun_gaussianCoeff_blocks [Finite ι] {κ : Type*} [Finite κ]
    (A : ι → E) (B : κ → E) (hAB : ∀ i j, ⟪A i, B j⟫ = 0) :
    IndepFun (fun w i => ⟪A i, w⟫) (fun w j => ⟪B j, w⟫) (stdGaussian E) := by
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  have hId : HasGaussianLaw (id : E → E) (stdGaussian E) := IsGaussian.hasGaussianLaw_id
  have hG : HasGaussianLaw
      (fun w : E => ((fun i => ⟪A i, w⟫), (fun j => ⟪B j, w⟫))) (stdGaussian E) :=
    hId.map_fun
      ((ContinuousLinearMap.pi (fun i => innerSL ℝ (A i))).prod
        (ContinuousLinearMap.pi (fun j => innerSL ℝ (B j))))
  apply hG.indepFun_of_covariance_eval
  intro i j
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian]
  exact hAB i j

variable {N : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

/-- The interaction/root coordinate map used by the tilted-mass observable. -/
noncomputable def pairGaussianDisorderRoot (S : Matrix (Config N) (Config N) ℝ)
    (w : EuclideanSpace ℝ (Config N ⊕ (Fin N × J))) :
    EnergySpace N × (Fin N × J → ℝ) :=
  (pairGaussianInteraction
      (fun σ => gaussianSqrtCoeff (pairDisorderRootCovariance S) (Sum.inl σ)) w,
    fun ij => ⟪gaussianSqrtCoeff (pairDisorderRootCovariance S) (Sum.inr ij), w⟫)

theorem measurable_pairGaussianDisorderRoot (S : Matrix (Config N) (Config N) ℝ) :
    Measurable (pairGaussianDisorderRoot (J := J) S) := by
  unfold pairGaussianDisorderRoot pairGaussianInteraction
  fun_prop

/-- The concrete Gaussian interaction and root coordinates have exactly
the product law of the physical Hamiltonian and independent root marks. -/
theorem map_pairGaussianDisorderRoot {S : Matrix (Config N) (Config N) ℝ}
    (hS : S.PosSemidef) :
    (stdGaussian (EuclideanSpace ℝ (Config N ⊕ (Fin N × J)))).map
        (pairGaussianDisorderRoot S) =
      (multivariateGaussian 0 S).prod (Measure.pi fun _ : Fin N × J => gaussianReal 0 1) := by
  let E := EuclideanSpace ℝ (Config N ⊕ (Fin N × J))
  let A := fun σ : Config N => gaussianSqrtCoeff (pairDisorderRootCovariance (J := J) S)
    (Sum.inl σ)
  let B := fun ij : Fin N × J => gaussianSqrtCoeff (pairDisorderRootCovariance S)
    (Sum.inr ij)
  have hA : ∀ σ τ, ⟪A σ, A τ⟫ = S σ τ := by
    intro σ τ
    exact inner_gaussianSqrtCoeff (posSemidef_pairDisorderRootCovariance hS) _ _
  have hB : ∀ i j, ⟪B i, B j⟫ = (1 : Matrix (Fin N × J) (Fin N × J) ℝ) i j := by
    intro i j
    exact inner_gaussianSqrtCoeff (posSemidef_pairDisorderRootCovariance hS) _ _
  have hAB : ∀ σ ij, ⟪A σ, B ij⟫ = 0 := by
    intro σ ij
    exact inner_gaussianSqrtCoeff (posSemidef_pairDisorderRootCovariance hS) _ _
  have hIndep : IndepFun (pairGaussianInteraction A) (fun w ij => ⟪B ij, w⟫)
      (stdGaussian E) :=
    (indepFun_gaussianCoeff_blocks A B hAB).comp (φ := WithLp.toLp 2) (ψ := id)
      (by fun_prop) measurable_id
  have hLawA : (stdGaussian E).map (pairGaussianInteraction A) =
      multivariateGaussian 0 S := map_stdGaussian_gaussianCoeffCLM A S hA
  have hLawB : (stdGaussian E).map (fun w ij => ⟪B ij, w⟫) =
      Measure.pi (fun _ : Fin N × J => gaussianReal 0 1) := by
    have he := map_stdGaussian_gaussianCoeffCLM B 1 hB
    rw [multivariateGaussian_zero_one, ← map_pi_eq_stdGaussian (ι := Fin N × J)] at he
    have hh := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin N × J)) =>
      μ.map (WithLp.ofLp : EuclideanSpace ℝ (Fin N × J) → Fin N × J → ℝ)) he
    rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)] at hh
    change (stdGaussian E).map (fun w ij => ⟪B ij, w⟫) =
      (Measure.pi (fun _ : Fin N × J => gaussianReal 0 1)).map id at hh
    simpa only [Measure.map_id] using hh
  have hmeasA : AEMeasurable (pairGaussianInteraction A) (stdGaussian E) := by
    change AEMeasurable (gaussianCoeffCLM A) (stdGaussian E)
    fun_prop
  have hh := hIndep.map_prod_eq_prod_map_map hmeasA (by fun_prop)
  rw [hLawA, hLawB] at hh
  exact hh

end SpinGlass
