import SpinGlass.Parisi.Coupled.CoupledAuxiliaryTransport

/-!
# Deleting deterministic marks from the physical cascade

A zero-variance Gaussian insertion is a deterministic zero vector. Its
positive-mass operation is the identity, so it can be removed from the
physical cascade without changing its constrained partition function.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- Removing one Dirac mark from a cascade is exact. The removed mass
must be nonzero; no ordering or variance positivity is required. -/
theorem cascadeRec_removeNth_dirac {T : Type*} [MeasurableSpace T] (k : ℕ) :
    ∀ (ms : Fin (k + 1) → ℝ) (μs : Fin (k + 1) → Measure T)
      [∀ i, IsProbabilityMeasure (μs i)] (p : Fin (k + 1)) (z : T),
      ms p ≠ 0 → μs p = Measure.dirac z →
      ∀ {G : (Fin (k + 1) → T) → ℝ≥0∞}, Measurable G →
      cascadeRec (k + 1) ms μs G =
        cascadeRec k (p.removeNth ms) (p.removeNth μs) (fun xs => G (p.insertNth z xs)) := by
  induction k with
  | zero =>
    intro ms μs _ p z hm hμ G hG
    have hp : p = 0 := Fin.ext (by omega)
    subst p
    rw [cascadeRec_succ, hμ]
    rw [lintegral_dirac' _ ((measurable_cascadeRec_cons 0 _ _ hG).pow_const _),
      ← ENNReal.rpow_mul, mul_one_div_cancel hm, ENNReal.rpow_one]
    simp only [cascadeRec_zero, Fin.insertNth_zero']
  | succ k ih =>
    intro ms μs _ p z hm hμ G hG
    cases p using Fin.cases with
    | zero =>
      rw [cascadeRec_succ]
      rw [hμ, lintegral_dirac' _ ((measurable_cascadeRec_cons (k + 1) _ _ hG).pow_const _),
        ← ENNReal.rpow_mul, mul_one_div_cancel hm, ENNReal.rpow_one]
      simp only [Fin.removeNth_zero, Fin.insertNth_zero']
    | succ q =>
      have hm0 : (q.succ.removeNth ms) 0 = ms 0 := by
        simp only [Fin.removeNth, Fin.succ_succAbove_zero]
      have hμ0 : (q.succ.removeNth μs) 0 = μs 0 := by
        simp only [Fin.removeNth, Fin.succ_succAbove_zero]
      have hmt : Fin.tail (q.succ.removeNth ms) = q.removeNth (Fin.tail ms) := by
        funext i
        simp only [Fin.tail, Fin.removeNth, Fin.succ_succAbove_succ]
      have hμt : Fin.tail (q.succ.removeNth μs) = q.removeNth (Fin.tail μs) := by
        funext i
        simp only [Fin.tail, Fin.removeNth, Fin.succ_succAbove_succ]
      rw [cascadeRec_succ, cascadeRec_succ, hm0, hμ0, hmt, hμt]
      congr 1
      apply lintegral_congr
      intro w
      have hGw : Measurable (fun zs => G (Fin.cons w zs)) :=
        hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id))
      rw [ih (Fin.tail ms) (Fin.tail μs) q z hm hμ (G := fun zs => G (Fin.cons w zs)) hGw]
      congr 2
      funext xs
      rw [Fin.insertNth_succ_cons]

/-- A finite product of zero-variance centered Gaussian coordinates is
the Dirac law at the zero vector. -/
theorem pi_gaussianReal_zero_eq_dirac {S : Type*} [Fintype S] :
    Measure.pi (fun _ : S => gaussianReal 0 0) = Measure.dirac (fun _ : S => (0 : ℝ)) := by
  classical
  simp only [gaussianReal_zero_var]
  apply Measure.pi_eq
  intro s hs
  by_cases hm : ∀ i, (0 : ℝ) ∈ s i
  · simp [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs),
      Measure.dirac_apply' _ (hs _), Set.mem_pi, hm]
  · obtain ⟨i, hi⟩ := not_forall.mp hm
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Measure.dirac_apply' _ (hs i), hi])]
    simp [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs), Set.mem_pi, hm]

/-- The zero auxiliary level disappears from the actual finite
Gaussian cascade, with its exact insertion coordinates retained. -/
theorem cascadeRec_siteGaussianMarks_remove_zero {S : Type*} [Fintype S] {k : ℕ}
    (ms : Fin (k + 1) → ℝ) (vs : Fin (k + 1) → ℝ≥0) (p : Fin (k + 1))
    (hm : ms p ≠ 0) (hv : vs p = 0) {G : (Fin (k + 1) → S → ℝ) → ℝ≥0∞}
    (hG : Measurable G) :
    cascadeRec (k + 1) ms (siteGaussianMarks S (k + 1) vs) G =
      cascadeRec k (p.removeNth ms) (siteGaussianMarks S k (p.removeNth vs))
        (fun xs => G (p.insertNth (fun _ => 0) xs)) := by
  have hμ : siteGaussianMarks S (k + 1) vs p = Measure.dirac (fun _ : S => (0 : ℝ)) := by
    rw [siteGaussianMarks, hv, pi_gaussianReal_zero_eq_dirac]
  exact cascadeRec_removeNth_dirac k ms (siteGaussianMarks S (k + 1) vs) p
    (fun _ => 0) hm hμ hG

/-- Inserting a zero field at a deleted level leaves the physical
paired branch partition function with the corresponding factor removed. -/
theorem pairHamG_insertNth_zero_eq {N k : ℕ} {J : Type*} [Fintype J]
    (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin (k + 1) → Fin 2 → J → ℝ) (p : Fin (k + 1))
    (z₀ : Fin N × J → ℝ) (xs : Fin k → Fin N × J → ℝ) :
    pairHamG N (k + 1) c H lam a K₀ K z₀ (p.insertNth (fun _ => 0) xs) =
      pairHamG N k c H lam a K₀ (p.removeNth K) z₀ xs := by
  have hmark (l : Fin 2) (i : Fin N) :
      pairBranchMark N (k + 1) K₀ K z₀ (p.insertNth (fun _ => 0) xs) l i =
        pairBranchMark N k K₀ (p.removeNth K) z₀ xs l i := by
    unfold pairBranchMark
    congr 1
    rw [Fin.sum_univ_succAbove _ p]
    simp only [Fin.insertNth_apply_same, mul_zero, Finset.sum_const_zero, zero_add,
      Fin.insertNth_apply_succAbove, Fin.removeNth]
  unfold pairHamG pairBranchZX pairBranchHamX
  simp_rw [hmark]

/-- The physical paired cascade with a zero auxiliary insertion is
exactly the shorter cascade under the original constrained partition sum. -/
theorem cascadeRec_pairHamG_remove_zero_eq {N k : ℕ} {J : Type*} [Fintype J]
    (ms : Fin (k + 1) → ℝ) (vs : Fin (k + 1) → ℝ≥0) (p : Fin (k + 1))
    (hm : ms p ≠ 0) (hv : vs p = 0)
    (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin (k + 1) → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) :
    cascadeRec (k + 1) ms (siteGaussianMarks (Fin N × J) (k + 1) vs)
        (pairHamG N (k + 1) c H lam a K₀ K z₀) =
      cascadeRec k (p.removeNth ms) (siteGaussianMarks (Fin N × J) k (p.removeNth vs))
        (pairHamG N k c H lam a K₀ (p.removeNth K) z₀) := by
  rw [cascadeRec_siteGaussianMarks_remove_zero ms vs p hm hv
    (measurable_pairHamG' N (k + 1) c H lam a K₀ K z₀)]
  simp_rw [pairHamG_insertNth_zero_eq]

end SpinGlass
