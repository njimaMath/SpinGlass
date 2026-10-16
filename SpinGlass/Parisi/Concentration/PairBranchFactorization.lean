import SpinGlass.Parisi.Concentration.ParisiTiltParameters

/-!
# Single-copy factorization of the original pair branch

The common-prefix factors split the unconstrained pair partition function
into two copies of the same single-replica partition function. Gaussian
site coordinates are rearranged without changing their product law.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N k : ℕ}

/-- A single branch with its interaction and Gaussian marks already
scaled by the interpolation coefficients. -/
noncomputable def unscaledHamG (N k : ℕ) (H : EnergySpace N)
    (h z : Fin N → ℝ) (x : Fin k → Fin N → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ σ : Config N,
    Real.exp (-(H σ + ∑ i, isingSpin (σ i) * (h i + z i + ∑ p, x p i))))

theorem measurable_unscaledHamG (H : EnergySpace N) (h z : Fin N → ℝ) :
    Measurable (unscaledHamG N k H h z) := by
  unfold unscaledHamG
  fun_prop

theorem unscaledHamG_pos (H : EnergySpace N) (h z : Fin N → ℝ)
    (x : Fin k → Fin N → ℝ) : 0 < unscaledHamG N k H h z x := by
  exact ENNReal.ofReal_pos.2 (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)

/-- Restoring the interpolation coefficients recovers the existing
single-branch partition function exactly, including both time endpoints. -/
theorem unscaledHamG_interpolation_eq_hamG (t : ℝ) (H : EnergySpace N)
    (h z : Fin N → ℝ) (x : Fin k → Fin N → ℝ) :
    unscaledHamG N k (Real.sqrt t • H) h (fun i => Real.sqrt (1 - t) * z i)
      (fun p i => Real.sqrt (1 - t) * x p i) = hamG N k t h H z x := by
  unfold unscaledHamG hamG branchZX
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  change -(Real.sqrt t * H σ + ∑ i, isingSpin (σ i) *
    (h i + Real.sqrt (1 - t) * z i + ∑ p, Real.sqrt (1 - t) * x p i)) =
      -branchHamX N k t h H z x σ
  have hi (i : Fin N) : isingSpin (σ i) *
      (h i + Real.sqrt (1 - t) * z i + ∑ p, Real.sqrt (1 - t) * x p i) =
      Real.sqrt (1 - t) * (isingSpin (σ i) * (z i + ∑ p, x p i)) + h i * isingSpin (σ i) := by
    rw [← Finset.mul_sum]
    ring
  simp_rw [hi, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold branchHamX
  ring

/-- Factoring the unconstrained pair branch requires no averaging. -/
theorem pairHamG_one_eq_prod {J : Type*} [Fintype J]
    (H : EnergySpace N) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) :
    pairHamG N k (fun _ => 1) H 0 a K₀ K z x =
      ∏ l : Fin 2, unscaledHamG N k H (fun i => a (i, l))
        (fun i => ∑ j, K₀ l j * z (i, j)) (fun p i => ∑ j, K p l j * x p (i, j)) := by
  classical
  let f := fun (l : Fin 2) (σ : Config N) =>
    Real.exp (-(H σ + ∑ i, isingSpin (σ i) * (a (i, l) + pairBranchMark N k K₀ K z x l i)))
  have hp : (∏ l : Fin 2, ∑ σ : Config N, f l σ) =
      ∑ σ : Fin 2 → Config N, ∏ l : Fin 2, f l (σ l) := Fintype.prod_sum f
  have hf : ∀ σ : Fin 2 → Config N,
      Real.exp (-pairBranchHamX N k H 0 a K₀ K z x σ) = ∏ l : Fin 2, f l (σ l) := by
    intro σ
    rw [Fin.prod_univ_two, ← Real.exp_add]
    congr 1
    simp only [pairBranchHamX, zero_mul, sub_zero, Fin.sum_univ_two]
    ring
  unfold pairHamG pairBranchZX
  simp only [one_mul, hf, ← hp]
  rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => Finset.sum_nonneg fun _ _ => Real.exp_nonneg _)]
  apply Finset.prod_congr rfl
  intro l _
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  simp only [pairBranchMark, add_assoc]

/-- Splitting the two independent Gaussian columns into two site vectors. -/
def splitSitePair (z : Fin N × Fin 2 → ℝ) : (Fin N → ℝ) × (Fin N → ℝ) :=
  (fun i => z (i, 0), fun i => z (i, 1))

theorem measurable_splitSitePair : Measurable (splitSitePair (N := N)) := by
  unfold splitSitePair
  fun_prop

theorem map_gaussian_splitSitePair (v : ℝ≥0) :
    (Measure.pi (fun _ : Fin N × Fin 2 => gaussianReal 0 v)).map splitSitePair =
      (Measure.pi (fun _ : Fin N => gaussianReal 0 v)).prod
        (Measure.pi (fun _ : Fin N => gaussianReal 0 v)) := by
  let curry := MeasurableEquiv.curry (Fin N) (Fin 2) ℝ
  let split := fun z : Fin N → Fin 2 → ℝ => fun i => MeasurableEquiv.finTwoArrow (z i)
  let pair := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin N)
  have he : splitSitePair (N := N) = pair ∘ split ∘ curry := rfl
  have hc : (Measure.pi (fun _ : Fin N × Fin 2 => gaussianReal 0 v)).map curry =
      Measure.pi (fun _ : Fin N => Measure.pi (fun _ : Fin 2 => gaussianReal 0 v)) := by
    simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry (fun _ : Fin N => fun _ : Fin 2 => gaussianReal 0 v)
  rw [he, ← Function.comp_assoc, ← Measure.map_map (by fun_prop) curry.measurable, hc,
    ← Measure.map_map pair.measurable (by fun_prop)]
  dsimp only [split]
  rw [Measure.pi_map_pi (fun _ => MeasurableEquiv.finTwoArrow.measurable.aemeasurable)]
  simp_rw [(measurePreserving_finTwoArrow (gaussianReal 0 v)).map_eq]
  exact (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N)
    (fun _ => gaussianReal 0 v) (fun _ => gaussianReal 0 v)).map_eq

/-- Evaluating one original common-prefix factor selects the common
column below the meeting level and the replica's own column above it. -/
theorem sum_couplingFactorSgn_one_mul (τ p : ℕ) (l : Fin 2) (z : Fin 2 → ℝ) :
    ∑ j, couplingFactorSgn 1 τ p l j * z j = if p < τ then z 0 else z l := by
  classical
  unfold couplingFactorSgn
  split_ifs <;> simp

/-- The original factors give the coupled product used by the abstract
pair-cascade identities. The root mark is common to both replicas. -/
theorem pairHamG_original_one_eq_coupled_product (r : ℕ)
    (H : EnergySpace N) (h : Fin N → ℝ) (z : Fin N × Fin 2 → ℝ)
    (x : Fin k → Fin N × Fin 2 → ℝ) :
    pairHamG N k (fun _ => 1) H 0 (sharedReplicaSiteField h)
      (couplingFactorSgn 1 (r + 1) 0)
      (fun p => couplingFactorSgn 1 (r + 1) (p.val + 1)) z x =
      unscaledHamG N k H h (fun i => z (i, 0))
        (fun p => (couplingMap r p.val (splitSitePair (x p))).1) *
      unscaledHamG N k H h (fun i => z (i, 0))
        (fun p => (couplingMap r p.val (splitSitePair (x p))).2) := by
  rw [pairHamG_one_eq_prod, Fin.prod_univ_two]
  apply congrArg₂ (· * ·)
  all_goals
    congr 1
    · funext i
      rw [sum_couplingFactorSgn_one_mul]
      simp
    · funext p i
      rw [sum_couplingFactorSgn_one_mul]
      simp only [Nat.add_lt_add_iff_right, couplingMap, splitSitePair]
      split_ifs <;> rfl

/-- The unconstrained original pair recursion equals the square of the
single-copy recursion, including every meeting level and zero variances. -/
theorem cascadeRec_pairHamG_original_one_eq_sq (r : ℕ)
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (H : EnergySpace N) (h : Fin N → ℝ) (z : Fin N × Fin 2 → ℝ) :
    cascadeRec k (halveBelow r ms) (siteGaussianMarks (Fin N × Fin 2) k vs)
      (pairHamG N k (fun _ => 1) H 0 (sharedReplicaSiteField h)
        (couplingFactorSgn 1 (r + 1) 0)
        (fun p => couplingFactorSgn 1 (r + 1) (p.val + 1)) z) =
      (cascadeRec k ms (gaussianMarks N k vs)
        (unscaledHamG N k H h (fun i => z (i, 0)))) ^ 2 := by
  let G := unscaledHamG N k H h (fun i => z (i, 0))
  let W := fun xs : Fin k → (Fin N → ℝ) × (Fin N → ℝ) =>
    G (fun p => (couplingMap r p.val (xs p)).1) * G (fun p => (couplingMap r p.val (xs p)).2)
  have hG : Measurable G := measurable_unscaledHamG _ _ _
  have hcouple : Measurable (fun xs : Fin k → (Fin N → ℝ) × (Fin N → ℝ) =>
      fun p => couplingMap r p.val (xs p)) := measurable_pi_lambda _ fun p =>
    (measurable_couplingMap r p.val).comp (measurable_pi_apply p)
  have hW : Measurable W := (hG.comp (measurable_pairFst.comp hcouple)).mul
    (hG.comp (measurable_pairSnd.comp hcouple))
  have hpoint : pairHamG N k (fun _ => 1) H 0 (sharedReplicaSiteField h)
      (couplingFactorSgn 1 (r + 1) 0)
      (fun p => couplingFactorSgn 1 (r + 1) (p.val + 1)) z =
      fun xs => W (fun p => splitSitePair (xs p)) := by
    funext xs
    exact pairHamG_original_one_eq_coupled_product r H h z xs
  have hmap : (fun p => (siteGaussianMarks (Fin N × Fin 2) k vs p).map splitSitePair) =
      fun p => (gaussianMarks N k vs p).prod (gaussianMarks N k vs p) := by
    funext p
    exact map_gaussian_splitSitePair (vs p)
  rw [hpoint, ← cascadeRec_map k (halveBelow r ms) _ (fun _ => splitSitePair)
    (fun _ => measurable_splitSitePair) hW, hmap]
  exact cascadeRec_coupling k r ms (gaussianMarks N k vs) hG hpos

/-- The corresponding logarithmic identity is twice the single-copy
recursion. No pressure comparison is assumed. -/
theorem log_cascadeRec_pairHamG_original_one_eq_two_mul (r : ℕ)
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (H : EnergySpace N) (h : Fin N → ℝ) (z : Fin N × Fin 2 → ℝ) :
    Real.log (cascadeRec k (halveBelow r ms) (siteGaussianMarks (Fin N × Fin 2) k vs)
      (pairHamG N k (fun _ => 1) H 0 (sharedReplicaSiteField h)
        (couplingFactorSgn 1 (r + 1) 0)
        (fun p => couplingFactorSgn 1 (r + 1) (p.val + 1)) z)).toReal =
      2 * Real.log (cascadeRec k ms (gaussianMarks N k vs)
        (unscaledHamG N k H h (fun i => z (i, 0)))).toReal := by
  rw [cascadeRec_pairHamG_original_one_eq_sq r ms vs hpos,
    ENNReal.toReal_pow, Real.log_pow]
  norm_num

end SpinGlass
