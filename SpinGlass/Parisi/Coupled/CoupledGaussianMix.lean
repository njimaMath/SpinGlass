import SpinGlass.Parisi.Coupled.CoupledVarianceWitness

/-!
# Laws of the normalized independent Gaussian contributions

The four independent driven/auxiliary columns reduce to two independent
Gaussian columns of the same total variance. The construction includes
zero total variance and does not divide by the driven variance.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- Combining two independent columns at each replica coordinate. -/
noncomputable def coupledVarianceMixMap (d e : ℝ≥0)
    (z : Fin 2 ⊕ Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => gaussianVarianceShare d e * z (.inl i) + gaussianVarianceShare e d * z (.inr i)

theorem measurable_coupledVarianceMixMap (d e : ℝ≥0) : Measurable (coupledVarianceMixMap d e) := by
  unfold coupledVarianceMixMap
  fun_prop

/-- A normalized sum of two independent marks has the total Gaussian
variance, including when that total is zero. -/
theorem map_gaussianReal_prod_varianceShare (d e : ℝ≥0) :
    ((gaussianReal 0 (d + e)).prod (gaussianReal 0 (d + e))).map
      (fun z : ℝ × ℝ => gaussianVarianceShare d e * z.1 + gaussianVarianceShare e d * z.2) =
      gaussianReal 0 (d + e) := by
  let c := gaussianVarianceShare d e
  let b := gaussianVarianceShare e d
  let μ := gaussianReal 0 (d + e)
  have hi : IndepFun (fun z : ℝ × ℝ => c * z.1) (fun z : ℝ × ℝ => b * z.2) (μ.prod μ) :=
    indepFun_prod (X := fun z : ℝ => c * z) (Y := fun z : ℝ => b * z)
      (by fun_prop) (by fun_prop)
  have hc : (μ.prod μ).map (fun z : ℝ × ℝ => c * z.1) =
      gaussianReal 0 (NNReal.mk (c ^ 2) (sq_nonneg c) * (d + e)) := by
    change (μ.prod μ).map ((fun z : ℝ => c * z) ∘ Prod.fst) = _
    rw [← Measure.map_map (by fun_prop) measurable_fst,
      measurePreserving_fst.map_eq, gaussianReal_map_const_mul, mul_zero]
  have hb : (μ.prod μ).map (fun z : ℝ × ℝ => b * z.2) =
      gaussianReal 0 (NNReal.mk (b ^ 2) (sq_nonneg b) * (d + e)) := by
    change (μ.prod μ).map ((fun z : ℝ => b * z) ∘ Prod.snd) = _
    rw [← Measure.map_map (by fun_prop) measurable_snd,
      measurePreserving_snd.map_eq, gaussianReal_map_const_mul, mul_zero]
  have hvar : NNReal.mk (c ^ 2) (sq_nonneg c) * (d + e) +
      NNReal.mk (b ^ 2) (sq_nonneg b) * (d + e) = d + e := by
    apply NNReal.eq
    change c ^ 2 * ((d + e : ℝ≥0) : ℝ) + b ^ 2 * ((d + e : ℝ≥0) : ℝ) = _
    have hh := gaussianVarianceShare_sum_covariance d e
    change ((d + e : ℝ≥0) : ℝ) * (c ^ 2 + b ^ 2) = (d : ℝ) + e at hh
    simpa only [NNReal.coe_add] using (show c ^ 2 * ((d + e : ℝ≥0) : ℝ) +
      b ^ 2 * ((d + e : ℝ≥0) : ℝ) = (d : ℝ) + e by nlinarith)
  have hh := gaussianReal_add_gaussianReal_of_indepFun hi hc hb
  simp only [zero_add, hvar] at hh
  exact hh

/-- The mixed replica coordinates are again independent Gaussians,
with exactly the total variance. -/
theorem map_pi_gaussianReal_coupledVarianceMixMap (d e : ℝ≥0) :
    (Measure.pi (fun _ : Fin 2 ⊕ Fin 2 => gaussianReal 0 (d + e))).map
      (coupledVarianceMixMap d e) =
      Measure.pi (fun _ : Fin 2 => gaussianReal 0 (d + e)) := by
  let μ := gaussianReal 0 (d + e)
  let f := fun z : ℝ × ℝ => gaussianVarianceShare d e * z.1 + gaussianVarianceShare e d * z.2
  let split := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)
  let pair := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 2)
  have hs : MeasurePreserving split (Measure.pi (fun _ : Fin 2 ⊕ Fin 2 => μ))
      ((Measure.pi (fun _ : Fin 2 => μ)).prod (Measure.pi (fun _ : Fin 2 => μ))) :=
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin 2 ⊕ Fin 2 => μ)).symm split.symm
  have hp : MeasurePreserving pair.symm
      ((Measure.pi (fun _ : Fin 2 => μ)).prod (Measure.pi (fun _ : Fin 2 => μ)))
      (Measure.pi (fun _ : Fin 2 => μ.prod μ)) :=
    (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 2)
      (fun _ => μ) (fun _ => μ)).symm pair
  have hmix : coupledVarianceMixMap d e =
      (fun z : Fin 2 → ℝ × ℝ => fun i => f (z i)) ∘ pair.symm ∘ split := rfl
  rw [hmix, ← Function.comp_assoc, ← Measure.map_map (by fun_prop) split.measurable, hs.map_eq,
    ← Measure.map_map (by fun_prop) pair.symm.measurable, hp.map_eq]
  rw [Measure.pi_map_pi (fun _ => (show Measurable f by fun_prop).aemeasurable)]
  congr 1
  funext i
  exact map_gaussianReal_prod_varianceShare d e

/-- Combining the independent columns commutes with every two-replica
linear factor. This is a pointwise identity before taking Gaussian laws. -/
theorem sum_coupledVarianceFactors_mul_eq_mix (d e : ℝ≥0) (K : Fin 2 → Fin 2 → ℝ)
    (z : Fin 2 ⊕ Fin 2 → ℝ) (l : Fin 2) :
    (∑ j, (coupledDrivenVarianceFactor d e K + coupledAuxVarianceFactor d e K) l j * z j) =
      ∑ j, K l j * coupledVarianceMixMap d e z j := by
  simp only [Pi.add_apply, coupledDrivenVarianceFactor, coupledAuxVarianceFactor,
    SpinGlass.sumL, SpinGlass.sumR, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, mul_zero, zero_add, add_zero, coupledVarianceMixMap]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual coupled terminal function under the four-column factors
is the original two-column terminal function under the mixed marks. -/
theorem pairSiteF_varianceShare_eq {κ : ℕ} (d₀ e₀ : ℝ≥0) (ds es : Fin κ → ℝ≥0)
    (K₀ : Fin 2 → Fin 2 → ℝ) (K : Fin κ → Fin 2 → Fin 2 → ℝ)
    (lam : ℝ) (h : Fin 2 → ℝ) (z₀ : Fin 2 ⊕ Fin 2 → ℝ)
    (zs : Fin κ → Fin 2 ⊕ Fin 2 → ℝ) :
    pairSiteF lam h (coupledDrivenVarianceFactor d₀ e₀ K₀ + coupledAuxVarianceFactor d₀ e₀ K₀)
        (fun p => coupledDrivenVarianceFactor (ds p) (es p) (K p) +
          coupledAuxVarianceFactor (ds p) (es p) (K p)) z₀ zs =
      pairSiteF lam h K₀ K (coupledVarianceMixMap d₀ e₀ z₀)
        (fun p => coupledVarianceMixMap (ds p) (es p) (zs p)) := by
  have hmark (l : Fin 2) :
      pairSiteMark (coupledDrivenVarianceFactor d₀ e₀ K₀ + coupledAuxVarianceFactor d₀ e₀ K₀)
        (fun p => coupledDrivenVarianceFactor (ds p) (es p) (K p) +
          coupledAuxVarianceFactor (ds p) (es p) (K p)) z₀ zs l =
      pairSiteMark K₀ K (coupledVarianceMixMap d₀ e₀ z₀)
        (fun p => coupledVarianceMixMap (ds p) (es p) (zs p)) l := by
    unfold pairSiteMark
    rw [sum_coupledVarianceFactors_mul_eq_mix]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    exact sum_coupledVarianceFactors_mul_eq_mix (ds p) (es p) (K p) (zs p) l
  unfold pairSiteF
  rw [hmark 0, hmark 1]

/-- Transport the whole coupled one-site recursion through the actual
Gaussian mixing law. The result holds at zero total variance and for every
coupling; it does not assume a zero-coupling or response-moment identity. -/
theorem pairSiteY₀_varianceShare_eq {κ : ℕ} (ns : Fin κ → ℝ)
    (d₀ e₀ : ℝ≥0) (ds es : Fin κ → ℝ≥0)
    (K₀ : Fin 2 → Fin 2 → ℝ) (K : Fin κ → Fin 2 → Fin 2 → ℝ)
    (lam : ℝ) (h : Fin 2 → ℝ) :
    pairSiteY₀ ns (d₀ + e₀) (fun p => ds p + es p) lam h
        (coupledDrivenVarianceFactor d₀ e₀ K₀ + coupledAuxVarianceFactor d₀ e₀ K₀)
        (fun p => coupledDrivenVarianceFactor (ds p) (es p) (K p) +
          coupledAuxVarianceFactor (ds p) (es p) (K p)) =
      pairSiteY₀ ns (d₀ + e₀) (fun p => ds p + es p) lam h K₀ K := by
  have hmap : (fun p => (siteGaussianMarks (Fin 2 ⊕ Fin 2) κ (fun p => ds p + es p) p).map
        (coupledVarianceMixMap (ds p) (es p))) =
      siteGaussianMarks (Fin 2) κ (fun p => ds p + es p) := by
    funext p
    exact map_pi_gaussianReal_coupledVarianceMixMap (ds p) (es p)
  have hpoint (z₀ : Fin 2 ⊕ Fin 2 → ℝ) :
      parisiRec κ ns (siteGaussianMarks (Fin 2 ⊕ Fin 2) κ (fun p => ds p + es p))
        (pairSiteF lam h (coupledDrivenVarianceFactor d₀ e₀ K₀ + coupledAuxVarianceFactor d₀ e₀ K₀)
          (fun p => coupledDrivenVarianceFactor (ds p) (es p) (K p) +
            coupledAuxVarianceFactor (ds p) (es p) (K p)) z₀) =
      parisiRec κ ns (siteGaussianMarks (Fin 2) κ (fun p => ds p + es p))
        (pairSiteF lam h K₀ K (coupledVarianceMixMap d₀ e₀ z₀)) := by
    have he : pairSiteF lam h
        (coupledDrivenVarianceFactor d₀ e₀ K₀ + coupledAuxVarianceFactor d₀ e₀ K₀)
        (fun p => coupledDrivenVarianceFactor (ds p) (es p) (K p) +
          coupledAuxVarianceFactor (ds p) (es p) (K p)) z₀ =
        fun zs => pairSiteF lam h K₀ K (coupledVarianceMixMap d₀ e₀ z₀)
          (fun p => coupledVarianceMixMap (ds p) (es p) (zs p)) := by
      funext zs
      exact pairSiteF_varianceShare_eq d₀ e₀ ds es K₀ K lam h z₀ zs
    rw [he, ← parisiRec_map κ ns _ (fun p => coupledVarianceMixMap (ds p) (es p))
      (fun p => measurable_coupledVarianceMixMap (ds p) (es p))
      (measurable_pairSiteF' lam h K₀ K (coupledVarianceMixMap d₀ e₀ z₀)), hmap]
  have hmeas : Measurable (fun z₀ : Fin 2 → ℝ =>
      parisiRec κ ns (siteGaussianMarks (Fin 2) κ (fun p => ds p + es p))
        (pairSiteF lam h K₀ K z₀)) := by
    have hG : Measurable (Function.uncurry fun (z₀ : Fin 2 → ℝ)
        (zs : Fin κ → Fin 2 → ℝ) => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K z₀ zs))) :=
      (continuous_pairSiteF lam h K₀ K).measurable.exp.ennreal_ofReal
    exact (measurable_cascadeRec_prod κ ns
      (siteGaussianMarks (Fin 2) κ (fun p => ds p + es p)) hG).ennreal_toReal.log
  unfold pairSiteY₀
  rw [integral_congr_ae (.of_forall hpoint)]
  have hi := integral_map (μ := Measure.pi (fun _ : Fin 2 ⊕ Fin 2 => gaussianReal 0 (d₀ + e₀)))
    (measurable_coupledVarianceMixMap d₀ e₀).aemeasurable
    hmeas.aestronglyMeasurable
  rw [map_pi_gaussianReal_coupledVarianceMixMap] at hi
  exact hi.symm

/-- The Gaussian recursion transport also holds after averaging any
common external-field law, with the same field in both replicas. -/
theorem randomFieldPairSiteY₀_varianceShare_eq {κ : ℕ} (μh : Measure ℝ) (ns : Fin κ → ℝ)
    (d₀ e₀ : ℝ≥0) (ds es : Fin κ → ℝ≥0)
    (K₀ : Fin 2 → Fin 2 → ℝ) (K : Fin κ → Fin 2 → Fin 2 → ℝ) (lam : ℝ) :
    randomFieldPairSiteY₀ μh ns (d₀ + e₀) (fun p => ds p + es p) lam
        (coupledDrivenVarianceFactor d₀ e₀ K₀ + coupledAuxVarianceFactor d₀ e₀ K₀)
        (fun p => coupledDrivenVarianceFactor (ds p) (es p) (K p) +
          coupledAuxVarianceFactor (ds p) (es p) (K p)) =
      randomFieldPairSiteY₀ μh ns (d₀ + e₀) (fun p => ds p + es p) lam K₀ K :=
  integral_congr_ae (.of_forall fun h => pairSiteY₀_varianceShare_eq ns d₀ e₀ ds es K₀ K lam (fun _ => h))

/-- The finite-volume coupled comparison after transporting the actual
driven/auxiliary marks to their two-column total-variance law. The covariance
increments of the driven field remain explicit inputs to this general bridge. -/
theorem coupled_bound_varianceShare_sameFactors_siteField {N κ : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    (hN : 0 < N) (ξ : ℝ → ℝ) (ρ : Fin 2 → Fin 2 → ℕ → ℝ) (u : ℝ)
    (hρ0 : ∀ l l', ρ l l' 0 = 0) {S : Set ℝ} (hρS : ∀ l l' r, ρ l l' r ∈ S)
    (htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q ∈ S, ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (h0 : deriv ξ 0 = 0)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (d₀ e₀ : ℝ≥0) (ds es : Fin κ → ℝ≥0)
    (K₀ : Fin 2 → Fin 2 → ℝ) (K : Fin κ → Fin 2 → Fin 2 → ℝ)
    (hC0 : ∀ l l', (d₀ : ℝ) * gram K₀ l l' = deriv ξ (ρ l l' 1) - deriv ξ (ρ l l' 0))
    (hC : ∀ (p : Fin κ) l l', (ds p : ℝ) * gram (K p) l l' =
      deriv ξ (ρ l l' (p.val + 2)) - deriv ξ (ρ l l' (p.val + 1)))
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ) (ns : Fin κ → ℝ)
    (hnsm : Monotone ns) (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1)
    (hu : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec κ ns
        (siteGaussianMarks (Fin N × (Fin 2 ⊕ Fin 2)) κ (fun p => ds p + es p))
        (coupledG N u a (coupledDrivenVarianceFactor d₀ e₀ K₀)
          (coupledAuxVarianceFactor d₀ e₀ K₀)
          (fun p => coupledDrivenVarianceFactor (ds p) (es p) (K p))
          (fun p => coupledAuxVarianceFactor (ds p) (es p) (K p)) ξ G₀ 1 θ)).toReal
        ∂Pm.prod (rootMarksLaw N (d₀ + e₀)) ≤
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, pairSiteY₀ ns (d₀ + e₀)
          (fun p => ds p + es p) lam (fun l => a (i, l)) K₀ K
        - lam * u - (1 / 2) * coupledLevelSum ξ ρ ns +
          pairDiagDefect ξ u (fun l l' => ρ l l' (κ + 1)) := by
  have hb := coupled_bound_varianceShare_siteField hN ξ ρ u hρ0 hρS htan h0 G₀
    d₀ e₀ ds es K₀ K₀ K K hC0 hC a lam ns hnsm hpos hle hu
  simp_rw [pairSiteY₀_varianceShare_eq] at hb
  exact hb

end SpinGlass
