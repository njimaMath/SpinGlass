import SpinGlass.Parisi.Coupled.CoupledProp

/-!
# Gaussian variance witnesses for coupled interpolation

The driven and auxiliary Gaussian fields use independent columns with the
total mark variance d+e. Normalizing their factors by that total realizes
the separate covariances d and e without a positive driven-variance
assumption. This covers zero time and closed overlap endpoints in (14.310).
-/

open MeasureTheory ProbabilityTheory Finset Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- Coefficient of a Gaussian contribution of variance d in a mark
whose total variance is d+e. The zero-total case has coefficient zero. -/
noncomputable def gaussianVarianceShare (d e : ℝ≥0) : ℝ :=
  Real.sqrt (d : ℝ) / Real.sqrt ((d + e : ℝ≥0) : ℝ)

/-- The normalization realizes the chosen variance even when it
or the total variance vanishes. -/
theorem gaussianVarianceShare_covariance (d e : ℝ≥0) :
    ((d + e : ℝ≥0) : ℝ) * gaussianVarianceShare d e ^ 2 = d := by
  by_cases hzero : d + e = 0
  · obtain ⟨hd, he⟩ := add_eq_zero.mp hzero
    simp [gaussianVarianceShare, hd, he]
  · have htotal : 0 < ((d + e : ℝ≥0) : ℝ) := by exact_mod_cast pos_iff_ne_zero.2 hzero
    unfold gaussianVarianceShare
    rw [div_pow, Real.sq_sqrt d.coe_nonneg, Real.sq_sqrt htotal.le]
    field_simp

/-- The two independent contributions add to the full covariance,
including the degenerate law concentrated at zero. -/
theorem gaussianVarianceShare_sum_covariance (d e : ℝ≥0) :
    ((d + e : ℝ≥0) : ℝ) *
      (gaussianVarianceShare d e ^ 2 + gaussianVarianceShare e d ^ 2) = d + e := by
  have hd := gaussianVarianceShare_covariance d e
  have he := gaussianVarianceShare_covariance e d
  rw [add_comm e d] at he
  nlinarith

/-- Driven fields occupy the first two independent Gaussian columns. -/
noncomputable def coupledDrivenVarianceFactor (d e : ℝ≥0) (K : Fin 2 → Fin 2 → ℝ) :
    Fin 2 → Fin 2 ⊕ Fin 2 → ℝ :=
  fun l j => gaussianVarianceShare d e * sumL (J' := Fin 2) K l j

/-- Auxiliary fields occupy the other two independent Gaussian columns. -/
noncomputable def coupledAuxVarianceFactor (d e : ℝ≥0) (K : Fin 2 → Fin 2 → ℝ) :
    Fin 2 → Fin 2 ⊕ Fin 2 → ℝ :=
  fun l j => gaussianVarianceShare e d * sumR K l j

/-- The driven columns have exactly their prescribed covariance. -/
theorem gram_coupledDrivenVarianceFactor (d e : ℝ≥0) (K : Fin 2 → Fin 2 → ℝ)
    (l l' : Fin 2) :
    ((d + e : ℝ≥0) : ℝ) * ∑ j, coupledDrivenVarianceFactor d e K l j *
      coupledDrivenVarianceFactor d e K l' j =
      (d : ℝ) * ∑ j, K l j * K l' j := by
  have hsum : (∑ j, coupledDrivenVarianceFactor d e K l j *
      coupledDrivenVarianceFactor d e K l' j) =
      gaussianVarianceShare d e ^ 2 * ∑ j, sumL (J' := Fin 2) K l j * sumL K l' j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [coupledDrivenVarianceFactor]
    ring
  have hgram := gram_sumL (J' := Fin 2) K l l'
  change (∑ j, sumL (J' := Fin 2) K l j * sumL K l' j) = ∑ j, K l j * K l' j at hgram
  rw [hsum, hgram, ← mul_assoc, gaussianVarianceShare_covariance]

/-- The auxiliary columns have exactly their prescribed covariance. -/
theorem gram_coupledAuxVarianceFactor (d e : ℝ≥0) (K : Fin 2 → Fin 2 → ℝ)
    (l l' : Fin 2) :
    ((d + e : ℝ≥0) : ℝ) * ∑ j, coupledAuxVarianceFactor d e K l j *
      coupledAuxVarianceFactor d e K l' j =
      (e : ℝ) * ∑ j, K l j * K l' j := by
  have hsum : (∑ j, coupledAuxVarianceFactor d e K l j *
      coupledAuxVarianceFactor d e K l' j) =
      gaussianVarianceShare e d ^ 2 * ∑ j, K l j * K l' j := by
    simp only [coupledAuxVarianceFactor, sumR, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum, ← mul_assoc]
  have he := gaussianVarianceShare_covariance e d
  rw [add_comm e d] at he
  rw [he]

/-- The driven factor vanishes on every auxiliary column. -/
theorem coupledDrivenVarianceFactor_inr (d e : ℝ≥0) (K : Fin 2 → Fin 2 → ℝ)
    (l j : Fin 2) : coupledDrivenVarianceFactor d e K l (.inr j) = 0 := by
  simp [coupledDrivenVarianceFactor, sumL]

/-- The auxiliary factor vanishes on every driven column. -/
theorem coupledAuxVarianceFactor_inl (d e : ℝ≥0) (K : Fin 2 → Fin 2 → ℝ)
    (l j : Fin 2) : coupledAuxVarianceFactor d e K l (.inl j) = 0 := by
  simp [coupledAuxVarianceFactor, sumR]

/-- Independent driven and auxiliary columns add their covariances.
Their two-replica factors may be different, as needed for signed root fields. -/
theorem gram_coupledVarianceFactors_add (d e : ℝ≥0) (K K' : Fin 2 → Fin 2 → ℝ)
    (l l' : Fin 2) :
    ((d + e : ℝ≥0) : ℝ) * gram
        (coupledDrivenVarianceFactor d e K + coupledAuxVarianceFactor d e K') l l' =
      (d : ℝ) * gram K l l' + (e : ℝ) * gram K' l l' := by
  have hsum : gram (coupledDrivenVarianceFactor d e K + coupledAuxVarianceFactor d e K') l l' =
      gram (coupledDrivenVarianceFactor d e K) l l' + gram (coupledAuxVarianceFactor d e K') l l' := by
    unfold gram
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    cases j with
    | inl j => simp [coupledAuxVarianceFactor_inl]
    | inr j => simp [coupledDrivenVarianceFactor_inr]
  rw [hsum, mul_add]
  exact congrArg₂ (· + ·) (gram_coupledDrivenVarianceFactor d e K l l')
    (gram_coupledAuxVarianceFactor d e K' l l')

/-- The actual finite-volume coupled theorem with separate driven and
auxiliary Gaussian variances. The chosen total marks allow zero driven
variance while preserving a nonzero auxiliary field. -/
theorem coupled_bound_varianceShare_siteField {N κ : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    (hN : 0 < N) (ξ : ℝ → ℝ) (ρ : Fin 2 → Fin 2 → ℕ → ℝ) (u : ℝ)
    (hρ0 : ∀ l l', ρ l l' 0 = 0) {S : Set ℝ} (hρS : ∀ l l' r, ρ l l' r ∈ S)
    (htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q ∈ S, ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (h0 : deriv ξ 0 = 0)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (d₀ e₀ : ℝ≥0) (ds es : Fin κ → ℝ≥0)
    (K₀ K₀' : Fin 2 → Fin 2 → ℝ) (K K' : Fin κ → Fin 2 → Fin 2 → ℝ)
    (hC0 : ∀ l l', (d₀ : ℝ) * gram K₀ l l' = deriv ξ (ρ l l' 1) - deriv ξ (ρ l l' 0))
    (hC : ∀ (p : Fin κ) l l', (ds p : ℝ) * gram (K p) l l' =
      deriv ξ (ρ l l' (p.val + 2)) - deriv ξ (ρ l l' (p.val + 1)))
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ) (ns : Fin κ → ℝ)
    (hnsm : Monotone ns) (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1)
    (hu : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec κ ns
        (siteGaussianMarks (Fin N × (Fin 2 ⊕ Fin 2)) κ (fun p => ds p + es p))
        (coupledG N u a (coupledDrivenVarianceFactor d₀ e₀ K₀)
          (coupledAuxVarianceFactor d₀ e₀ K₀')
          (fun p => coupledDrivenVarianceFactor (ds p) (es p) (K p))
          (fun p => coupledAuxVarianceFactor (ds p) (es p) (K' p)) ξ G₀ 1 θ)).toReal
        ∂Pm.prod (rootMarksLaw N (d₀ + e₀)) ≤
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, pairSiteY₀ ns (d₀ + e₀)
          (fun p => ds p + es p) lam (fun l => a (i, l))
          (coupledDrivenVarianceFactor d₀ e₀ K₀ + coupledAuxVarianceFactor d₀ e₀ K₀')
          (fun p => coupledDrivenVarianceFactor (ds p) (es p) (K p) +
            coupledAuxVarianceFactor (ds p) (es p) (K' p))
        - lam * u - (1 / 2) * coupledLevelSum ξ ρ ns +
          pairDiagDefect ξ u (fun l l' => ρ l l' (κ + 1)) := by
  have hb := coupled_bound'_of_monotone N hN ξ ρ u hρ0 hρS htan h0 G₀
    (d₀ + e₀) (fun p => ds p + es p) (J₁ := leftCols (Fin 2))
    (L₀ := coupledDrivenVarianceFactor d₀ e₀ K₀)
    (L₀' := coupledAuxVarianceFactor d₀ e₀ K₀')
    (L := fun p => coupledDrivenVarianceFactor (ds p) (es p) (K p))
    (L' := fun p => coupledAuxVarianceFactor (ds p) (es p) (K' p))
    (fun l l' => (gram_coupledDrivenVarianceFactor d₀ e₀ K₀ l l').trans (hC0 l l'))
    (fun p l l' => (gram_coupledDrivenVarianceFactor (ds p) (es p) (K p) l l').trans (hC p l l'))
    (fun l j hj => by simp [coupledDrivenVarianceFactor, sumL_of_not_mem_leftCols K₀ l hj])
    (fun p l j hj => by
      simp [coupledDrivenVarianceFactor, sumL_of_not_mem_leftCols (K p) l hj])
    (fun l j hj => by simp [coupledAuxVarianceFactor, sumR_of_mem_leftCols K₀' l hj])
    (fun p l j hj => by simp [coupledAuxVarianceFactor, sumR_of_mem_leftCols (K' p) l hj])
    a lam ns hnsm hpos hle hu
  rw [integral_parisiRec_pairCoshF_siteField N ns hpos hle] at hb
  exact hb

end SpinGlass
