import SpinGlass.Parisi.Concentration.PairBranchFactorization
import SpinGlass.Parisi.Coupled.Derivative.Transport

/-!
# The tilted mass and the branch-meeting identity

The original two-column Gaussian construction gives exactly the coupled
tilt in the cascade pair identity. The constrained pair function retains
the spin constraint before either tree or Gaussian averaging.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N k : ℕ}

/-- The constrained pair partition function on two specified branches,
with a common root field and independent positive-level arguments. -/
noncomputable def unscaledPairHamG (N k : ℕ) (c : (Fin 2 → Config N) → ℝ)
    (H : EnergySpace N) (h z : Fin N → ℝ)
    (x : Fin k → (Fin N → ℝ) × (Fin N → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ σ : Fin 2 → Config N, c σ * Real.exp (-(
    H (σ 0) + H (σ 1) +
      (∑ i, isingSpin (σ 0 i) * (h i + z i + ∑ p, (x p).1 i)) +
      (∑ i, isingSpin (σ 1 i) * (h i + z i + ∑ p, (x p).2 i)))))

theorem measurable_unscaledPairHamG (c : (Fin 2 → Config N) → ℝ)
    (H : EnergySpace N) (h z : Fin N → ℝ) :
    Measurable (unscaledPairHamG N k c H h z) := by
  unfold unscaledPairHamG
  fun_prop

/-- The actual common-prefix factors agree with the abstract coupling
map even for a constrained partition function. -/
theorem pairHamG_original_eq_unscaledPairHamG (r : ℕ)
    (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (h : Fin N → ℝ)
    (z : Fin N × Fin 2 → ℝ) (x : Fin k → Fin N × Fin 2 → ℝ) :
    pairHamG N k c H 0 (sharedReplicaSiteField h)
      (couplingFactorSgn 1 (r + 1) 0)
      (fun p => couplingFactorSgn 1 (r + 1) (p.val + 1)) z x =
      unscaledPairHamG N k c H h (fun i => z (i, 0))
        (fun p => couplingMap r p.val (splitSitePair (x p))) := by
  have hmark (l : Fin 2) (i : Fin N) :
      pairBranchMark N k (couplingFactorSgn 1 (r + 1) 0)
        (fun p => couplingFactorSgn 1 (r + 1) (p.val + 1)) z x l i =
        z (i, 0) + ∑ p, if p.val < r then x p (i, 0) else x p (i, l) := by
    simp only [pairBranchMark, sum_couplingFactorSgn_one_mul, Nat.zero_lt_succ,
      ite_true, Nat.add_lt_add_iff_right]
  have hfst (p : Fin k) (i : Fin N) :
      (couplingMap r p.val (splitSitePair (x p))).1 i =
        if p.val < r then x p (i, 0) else x p (i, 0) := by
    unfold couplingMap splitSitePair
    split_ifs <;> rfl
  have hsnd (p : Fin k) (i : Fin N) :
      (couplingMap r p.val (splitSitePair (x p))).2 i =
        if p.val < r then x p (i, 0) else x p (i, 1) := by
    unfold couplingMap splitSitePair
    split_ifs <;> rfl
  unfold pairHamG pairBranchZX unscaledPairHamG
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 2
  simp only [pairBranchHamX, zero_mul, sub_zero, Fin.sum_univ_two,
    sharedReplicaSiteField, hmark, hfst, hsnd, add_assoc]

/-- The unconstrained two-branch function factors before averaging. -/
theorem unscaledPairHamG_one_eq_prod (H : EnergySpace N) (h z : Fin N → ℝ)
    (x : Fin k → (Fin N → ℝ) × (Fin N → ℝ)) :
    unscaledPairHamG N k (fun _ => 1) H h z x =
      unscaledHamG N k H h z (fun p => (x p).1) *
        unscaledHamG N k H h z (fun p => (x p).2) := by
  let zr : Fin N × Fin 2 → ℝ := fun ij => z ij.1
  let xr : Fin k → Fin N × Fin 2 → ℝ := fun p ij =>
    if ij.2 = 0 then (x p).1 ij.1 else (x p).2 ij.1
  have hsplit (p : Fin k) : splitSitePair (xr p) = x p := by
    ext i <;> simp [splitSitePair, xr]
  have he := pairHamG_original_eq_unscaledPairHamG 0 (fun _ => 1) H h zr xr
  have hp := pairHamG_original_one_eq_coupled_product 0 H h zr xr
  simp only [couplingMap, Nat.not_lt_zero, ite_false, id_eq, hsplit, zr] at he hp
  exact he.symm.trans hp

/-- Every single-copy branch partition has a finite Gaussian mean. -/
theorem lintegral_unscaledHamG_ne_top (vs : Fin k → ℝ≥0)
    (H : EnergySpace N) (h z : Fin N → ℝ) :
    (∫⁻ x, unscaledHamG N k H h z x ∂Measure.pi (gaussianMarks N k vs)) ≠ ∞ := by
  have he (x : Fin k → Fin N → ℝ) : unscaledHamG N k H h z x =
      ∑ σ : Config N, ENNReal.ofReal (Real.exp (
        -(H σ + ∑ i, isingSpin (σ i) * (h i + z i)) +
          ∑ p, ∑ i, (-isingSpin (σ i)) * x p i)) := by
    unfold unscaledHamG
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
    apply Finset.sum_congr rfl
    intro σ _
    congr 2
    simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum, neg_mul,
      Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    ring
  simp_rw [he]
  exact lintegral_sum_ofReal_exp_gaussianMarks N k vs _ _

/-- Exact transport of both the weight and observable from the original
two-column Gaussians to the abstract common-prefix pair law. -/
theorem cascadeTilt_original_pair_gaussian_eq (r : ℕ)
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {G A : (Fin k → (Fin N → ℝ) × (Fin N → ℝ)) → ℝ≥0∞}
    (hG : Measurable G) (hA : Measurable A) :
    cascadeTilt k ms (siteGaussianMarks (Fin N × Fin 2) k vs)
      (fun x => G (fun p => couplingMap r p.val (splitSitePair (x p))))
      (fun x => A (fun p => couplingMap r p.val (splitSitePair (x p)))) =
      cascadeTilt k ms (pairMarkLaw r (gaussianMarks N k vs)) G A := by
  let φ : Fin k → (Fin N × Fin 2 → ℝ) → (Fin N → ℝ) × (Fin N → ℝ) :=
    fun p => couplingMap r p.val ∘ splitSitePair
  have hφ (p : Fin k) : Measurable (φ p) :=
    (measurable_couplingMap r p.val).comp measurable_splitSitePair
  have hmap : coordinateMapLaw (siteGaussianMarks (Fin N × Fin 2) k vs) φ hφ =
      pairMarkLaw r (gaussianMarks N k vs) := by
    funext p
    dsimp only [coordinateMapLaw, φ]
    rw [← Measure.map_map (measurable_couplingMap r p.val) measurable_splitSitePair]
    change ((Measure.pi (fun _ : Fin N × Fin 2 => gaussianReal 0 (vs p))).map
      splitSitePair).map (couplingMap r p.val) = _
    rw [map_gaussian_splitSitePair]
    exact congrFun (map_couplingMap_prod_eq_pairMarkLaw r (gaussianMarks N k vs)) p
  exact (cascadeTilt_coordinateMap k ms (siteGaussianMarks (Fin N × Fin 2) k vs)
    φ hφ hG hA).symm.trans (cascadeTilt_congr_measure ms hmap G A)

/-- The original constrained tilted mass is the coupled tilt of the
actual two-branch Gibbs numerator divided by the product partition. -/
theorem pairHamConstrainedTiltMass_original_eq (r : ℕ)
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (c : (Fin 2 → Config N) → ℝ)
    (H : EnergySpace N) (h : Fin N → ℝ) (z : Fin N × Fin 2 → ℝ) :
    pairHamConstrainedTiltMass (halveBelow r ms) vs c H 0 (sharedReplicaSiteField h)
      (couplingFactorSgn 1 (r + 1) 0)
      (fun p => couplingFactorSgn 1 (r + 1) (p.val + 1)) z =
      cascadeTilt k (halveBelow r ms) (pairMarkLaw r (gaussianMarks N k vs))
        (fun x => unscaledHamG N k H h (fun i => z (i, 0)) (fun p => (x p).1) *
          unscaledHamG N k H h (fun i => z (i, 0)) (fun p => (x p).2))
        (fun x => unscaledPairHamG N k c H h (fun i => z (i, 0)) x /
          (unscaledHamG N k H h (fun i => z (i, 0)) (fun p => (x p).1) *
            unscaledHamG N k H h (fun i => z (i, 0)) (fun p => (x p).2))) := by
  let G := unscaledHamG N k H h (fun i => z (i, 0))
  have hG : Measurable G := measurable_unscaledHamG _ _ _
  have hprod : Measurable (fun x : Fin k → (Fin N → ℝ) × (Fin N → ℝ) =>
      G (fun p => (x p).1) * G (fun p => (x p).2)) :=
    (hG.comp measurable_pairFst).mul (hG.comp measurable_pairSnd)
  have hfun (d : (Fin 2 → Config N) → ℝ) :
      pairHamG N k d H 0 (sharedReplicaSiteField h) (couplingFactorSgn 1 (r + 1) 0)
        (fun p => couplingFactorSgn 1 (r + 1) (p.val + 1)) z =
        fun x => unscaledPairHamG N k d H h (fun i => z (i, 0))
          (fun p => couplingMap r p.val (splitSitePair (x p))) :=
    funext (pairHamG_original_eq_unscaledPairHamG r d H h z)
  unfold pairHamConstrainedTiltMass
  simp_rw [hfun, unscaledPairHamG_one_eq_prod]
  exact cascadeTilt_original_pair_gaussian_eq r (halveBelow r ms) vs hprod
    ((measurable_unscaledPairHamG c H h (fun i => z (i, 0))).div hprod)

/-- The exact branch-meeting identity with the original Gaussian tilted
mass. This is a joint constrained mass, so no conditioning denominator
or division by a meeting probability is introduced. -/
theorem lintegral_unscaledPairHamG_succ_add_tilt
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (c : (Fin 2 → Config N) → ℝ)
    (H : EnergySpace N) (h : Fin N → ℝ) (z : Fin N × Fin 2 → ℝ) :
    let G := unscaledHamG N k H h (fun i => z (i, 0))
    let U := unscaledPairHamG N k c H h (fun i => z (i, 0))
    (∫⁻ ω, cascadeSqPair k (r.val + 1) U ω * (cascadeSum k G ω)⁻¹ ^ 2
      ∂cascadeLaw k ms (gaussianMarks N k vs)) +
      ENNReal.ofReal (mExt ms (r.val + 1) - mExt ms r.val) *
        pairHamConstrainedTiltMass (halveBelow r.val ms) vs c H 0 (sharedReplicaSiteField h)
          (couplingFactorSgn 1 (r.val + 1) 0)
          (fun p => couplingFactorSgn 1 (r.val + 1) (p.val + 1)) z =
      ∫⁻ ω, cascadeSqPair k r.val U ω * (cascadeSum k G ω)⁻¹ ^ 2
        ∂cascadeLaw k ms (gaussianMarks N k vs) := by
  dsimp only
  rw [pairHamConstrainedTiltMass_original_eq]
  exact lintegral_cascadeSqPair_succ_add_tilt k ms (gaussianMarks N k vs)
    (measurable_unscaledPairHamG c H h _) (measurable_unscaledHamG H h _)
    (unscaledHamG_pos H h _) (lintegral_unscaledHamG_ne_top vs H h _)
    hm.1 hm.2.1 hm.2.2 (by omega)

end SpinGlass
