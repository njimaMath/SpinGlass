import SpinGlass.Parisi.Guerra.GuerraFixedWeights
import SpinGlass.Parisi.Tree.LevelBound.Convergence
import SpinGlass.FiniteGibbs.GaussianFieldExpMoment

/-!
# Gaussian branch moments for the pressure limit

The disorder, root and positive-level marks all remain in the actual
interpolation law. The site field is fixed here, so no exponential moment
of its eventual probability law is required.
-/

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

theorem measurable_hamG_fixedTime (t : ℝ) (h : Fin N → ℝ) :
    Measurable (uncurry (fun q : EnergySpace N × (Fin N → ℝ) =>
      hamG N k t h q.1 q.2)) := by
  unfold uncurry hamG branchZX branchHamX
  fun_prop

/-- Finite mean of the actual branch partition, including interaction
disorder and all Gaussian marks. The deterministic field is arbitrary. -/
theorem lintegral_lintegral_hamG_ne_top
    (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (t : ℝ) (h : Fin N → ℝ) :
    (∫⁻ q, ∫⁻ x, hamG N k t h q.1 q.2 x ∂Measure.pi (gaussianMarks N k vs)
      ∂(gaussField N (overlapCovMatrix N ξ)).prod
        (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀))) ≠ ∞ := by
  classical
  let B := fun σ : Config N => fun i : Fin N => -Real.sqrt (1 - t) * isingSpin (σ i)
  let A := fun H : EnergySpace N => fun σ : Config N =>
    -Real.sqrt t * H σ - ∑ i, h i * isingSpin (σ i)
  let C := fun σ : Config N =>
    ENNReal.ofReal (Real.exp (∑ p : Fin k, ∑ i : Fin N, (vs p : ℝ) * B σ i ^ 2 / 2))
  have he (H : EnergySpace N) (z : Fin N → ℝ) (x : Fin k → Fin N → ℝ) :
      hamG N k t h H z x = ∑ σ : Config N,
        ENNReal.ofReal (Real.exp (A H σ + ∑ i, B σ i * z i +
          ∑ p : Fin k, ∑ i : Fin N, B σ i * x p i)) := by
    rw [hamG_eq_sum]
    apply Finset.sum_congr rfl
    intro σ _
    congr 2
    have hz : (∑ i, B σ i * z i) =
        -(Real.sqrt (1 - t) * ∑ i, isingSpin (σ i) * z i) := by
      dsimp only [B]
      simp only [neg_mul, mul_assoc, Finset.sum_neg_distrib, Finset.mul_sum]
    change -(Real.sqrt t * H σ + Real.sqrt (1 - t) *
      ∑ i, isingSpin (σ i) * z i + ∑ i, h i * isingSpin (σ i)) +
        (∑ p : Fin k, ∑ i : Fin N, B σ i * x p i) =
      (-Real.sqrt t * H σ - ∑ i, h i * isingSpin (σ i)) +
        (∑ i, B σ i * z i) + (∑ p : Fin k, ∑ i : Fin N, B σ i * x p i)
    rw [hz]
    ring
  have hx (q : EnergySpace N × (Fin N → ℝ)) :
      (∫⁻ x, hamG N k t h q.1 q.2 x ∂Measure.pi (gaussianMarks N k vs)) =
        ∑ σ : Config N, ENNReal.ofReal (Real.exp (A q.1 σ + ∑ i, B σ i * q.2 i)) * C σ := by
    simp_rw [he]
    rw [lintegral_finsetSum _ fun σ _ =>
      measurable_ofReal_exp_add_sum_mul (Fin N) k _ _]
    exact Finset.sum_congr rfl fun σ _ =>
      lintegral_ofReal_exp_add_gaussianMarks N k vs _ _
  have hterm (σ : Config N) : Measurable (fun q : EnergySpace N × (Fin N → ℝ) =>
      ENNReal.ofReal (Real.exp (A q.1 σ + ∑ i, B σ i * q.2 i)) * C σ) := by
    dsimp only [A]
    fun_prop
  simp_rw [hx]
  rw [lintegral_finsetSum _ fun σ _ => hterm σ]
  apply ENNReal.sum_ne_top.2
  intro σ _
  rw [lintegral_prod _ (hterm σ).aemeasurable]
  have hz (H : EnergySpace N) :
      (∫⁻ z, ENNReal.ofReal (Real.exp (A H σ + ∑ i, B σ i * z i)) * C σ
        ∂Measure.pi (fun _ : Fin N => gaussianReal 0 v₀)) =
        ENNReal.ofReal (Real.exp (A H σ)) *
          ENNReal.ofReal (Real.exp (∑ i, (v₀ : ℝ) * B σ i ^ 2 / 2)) * C σ := by
    rw [lintegral_mul_const _ (by fun_prop), lintegral_ofReal_exp_add_pi_gaussianReal]
  simp_rw [hz]
  have hA : Measurable (fun H : EnergySpace N => ENNReal.ofReal (Real.exp (A H σ))) := by
    dsimp only [A]
    fun_prop
  rw [lintegral_mul_const _ (hA.mul_const _), lintegral_mul_const _ hA]
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top _ ENNReal.ofReal_ne_top
    have hdis : (∫⁻ H, ENNReal.ofReal (Real.exp (-Real.sqrt t * H σ))
        ∂gaussField N (overlapCovMatrix N ξ)) ≠ ∞ := by
      have hh := GaussianField.lintegral_ofReal_exp_neg_smul_add_ne_top
        (GaussianField.ofMultivariateGaussian hS) (Real.sqrt t / 2) σ σ
      convert hh using 1
      congr 1
      funext H
      congr 2
      change -Real.sqrt t * H σ = -((Real.sqrt t / 2) * H σ + (Real.sqrt t / 2) * H σ)
      ring
    have hf (H : EnergySpace N) : ENNReal.ofReal (Real.exp (A H σ)) =
        ENNReal.ofReal (Real.exp (-Real.sqrt t * H σ)) *
          ENNReal.ofReal (Real.exp (-(∑ i, h i * isingSpin (σ i)))) := by
      dsimp only [A]
      rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    simp_rw [hf]
    rw [lintegral_mul_const _ (by fun_prop)]
    exact ENNReal.mul_ne_top hdis ENNReal.ofReal_ne_top
  · exact ENNReal.ofReal_ne_top

/-- The actual cascade partition has a finite Gaussian mean at every
fixed weight sample of finite total mass. -/
theorem lintegral_cascadeSum_hamG_ne_top
    (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (t : ℝ) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hW : weightSum k w ≠ ∞) :
    (∫⁻ q : (EnergySpace N × (Fin N → ℝ)) × CascadeMarks (Fin N → ℝ) k,
      cascadeSum k (hamG N k t h q.1.1 q.1.2) (cascadeZip k (w, q.2))
      ∂((gaussField N (overlapCovMatrix N ξ)).prod
        (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀))).prod
          (cascadeMarksLaw k (gaussianMarks N k vs))) ≠ ∞ := by
  have hG := measurable_hamG_fixedTime N k t h
  have hGt : Measurable (fun q : (ℝ × (EnergySpace N × (Fin N → ℝ))) ×
      (Fin k → Fin N → ℝ) => hamG N k t h q.1.2.1 q.1.2.2 q.2) :=
    by
      unfold hamG branchZX branchHamX
      fun_prop
  have hm : Measurable (fun q : (EnergySpace N × (Fin N → ℝ)) ×
      CascadeMarks (Fin N → ℝ) k =>
        cascadeSum k (hamG N k t h q.1.1 q.1.2) (cascadeZip k (w, q.2))) :=
    measurable_cascadeSum_of k
      (fun (_ : ℝ) (q : EnergySpace N × (Fin N → ℝ)) => hamG N k t h q.1 q.2) hGt w 0
  rw [lintegral_prod _ hm.aemeasurable]
  have he (q : EnergySpace N × (Fin N → ℝ)) :
      (∫⁻ z, cascadeSum k (hamG N k t h q.1 q.2) (cascadeZip k (w, z))
        ∂cascadeMarksLaw k (gaussianMarks N k vs)) =
        weightSum k w * ∫⁻ x, hamG N k t h q.1 q.2 x ∂Measure.pi (gaussianMarks N k vs) :=
    lintegral_cascadeSum_cascadeZip k _ w (measurable_hamG' N k t h q.1 q.2)
  simp_rw [he]
  have hi : Measurable (fun q : EnergySpace N × (Fin N → ℝ) =>
      ∫⁻ x, hamG N k t h q.1 q.2 x ∂Measure.pi (gaussianMarks N k vs)) :=
    Measurable.lintegral_prod_right' (f := fun q : (EnergySpace N × (Fin N → ℝ)) ×
      (Fin k → Fin N → ℝ) => hamG N k t h q.1.1 q.1.2 q.2) hG
  rw [lintegral_const_mul _ hi]
  exact ENNReal.mul_ne_top hW (lintegral_lintegral_hamG_ne_top N k ξ hS v₀ vs t h)

end

end SpinGlass
