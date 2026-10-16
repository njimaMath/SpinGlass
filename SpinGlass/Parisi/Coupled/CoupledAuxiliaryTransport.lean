import SpinGlass.Parisi.Coupled.CoupledRandomFieldComparison
import Common.Mathlib.Probability.PointProcess.CascadeBranchLaw

/-!
# Transport to the physical auxiliary marks

At the physical endpoint of the coupled comparison the driven mark factors
vanish. Projecting and rescaling the remaining independent columns gives
exactly their prescribed auxiliary Gaussian law, including zero variances.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The surviving auxiliary columns of a realized physical mark. -/
noncomputable def coupledAuxMarksMap {S : Type*} (d e : ℝ≥0)
    (z : S × (Fin 2 ⊕ Fin 2) → ℝ) : S × Fin 2 → ℝ :=
  fun s => gaussianVarianceShare e d * z (s.1, .inr s.2)

theorem measurable_coupledAuxMarksMap {S : Type*} (d e : ℝ≥0) :
    Measurable (coupledAuxMarksMap (S := S) d e) := by
  unfold coupledAuxMarksMap
  fun_prop

/-- The rescaled auxiliary coordinate has variance e even when d is zero. -/
theorem map_gaussianReal_auxVarianceShare (d e : ℝ≥0) :
    (gaussianReal 0 (d + e)).map (fun z => gaussianVarianceShare e d * z) =
      gaussianReal 0 e := by
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.eq
  change gaussianVarianceShare e d ^ 2 * ((d + e : ℝ≥0) : ℝ) = e
  have hh := gaussianVarianceShare_covariance e d
  simpa only [NNReal.coe_add, add_comm, mul_comm] using hh

/-- Projection preserves independence across sites and replicas. -/
theorem map_pi_gaussianReal_coupledAuxMarksMap {S : Type*} [Fintype S] (d e : ℝ≥0) :
    (Measure.pi (fun _ : S × (Fin 2 ⊕ Fin 2) => gaussianReal 0 (d + e))).map
      (coupledAuxMarksMap d e) =
      Measure.pi (fun _ : S × Fin 2 => gaussianReal 0 e) := by
  classical
  let proj := fun z : S × (Fin 2 ⊕ Fin 2) → ℝ => fun s : S × Fin 2 => z (s.1, .inr s.2)
  have hp : Measurable proj := by fun_prop
  have hinj : Function.Injective (fun s : S × Fin 2 => ((s.1, Sum.inr s.2) : S × (Fin 2 ⊕ Fin 2))) := by
    intro x y h
    have hx := congrArg Prod.fst h
    have hy := Sum.inr.inj (congrArg Prod.snd h)
    exact Prod.ext hx hy
  have hproj : (Measure.pi (fun _ : S × (Fin 2 ⊕ Fin 2) => gaussianReal 0 (d + e))).map proj =
      Measure.pi (fun _ : S × Fin 2 => gaussianReal 0 (d + e)) := by
    simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_comp_injective (fun _ : S × (Fin 2 ⊕ Fin 2) => gaussianReal 0 (d + e)) hinj
  change ((Measure.pi (fun _ : S × (Fin 2 ⊕ Fin 2) => gaussianReal 0 (d + e))).map
    ((fun z : S × Fin 2 → ℝ => fun s => gaussianVarianceShare e d * z s) ∘ proj)) = _
  rw [← Measure.map_map (by fun_prop) hp, hproj,
    Measure.pi_map_pi (fun _ => (show Measurable (fun z : ℝ => gaussianVarianceShare e d * z) by
      fun_prop).aemeasurable)]
  congr 1
  funext s
  exact map_gaussianReal_auxVarianceShare d e

theorem sum_coupledAuxVarianceFactor_mul_eq {S : Type*} (d e : ℝ≥0)
    (K : Fin 2 → Fin 2 → ℝ) (z : S × (Fin 2 ⊕ Fin 2) → ℝ) (l : Fin 2) (i : S) :
    (∑ j, coupledAuxVarianceFactor d e K l j * z (i, j)) =
      ∑ j, K l j * coupledAuxMarksMap d e z (i, j) := by
  simp only [coupledAuxVarianceFactor, sumR, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
    coupledAuxMarksMap]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The constrained physical terminal partition function is transported
pointwise, before taking any cascade or disorder expectations. -/
theorem pairHamG_auxVarianceShare_eq {N κ : ℕ} (c : (Fin 2 → Config N) → ℝ)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (d₀ e₀ : ℝ≥0) (ds es : Fin κ → ℝ≥0)
    (K₀ : Fin 2 → Fin 2 → ℝ) (K : Fin κ → Fin 2 → Fin 2 → ℝ)
    (z₀ : Fin N × (Fin 2 ⊕ Fin 2) → ℝ) (zs : Fin κ → Fin N × (Fin 2 ⊕ Fin 2) → ℝ) :
    pairHamG N κ c H lam a (coupledAuxVarianceFactor d₀ e₀ K₀)
        (fun p => coupledAuxVarianceFactor (ds p) (es p) (K p)) z₀ zs =
      pairHamG N κ c H lam a K₀ K (coupledAuxMarksMap d₀ e₀ z₀)
        (fun p => coupledAuxMarksMap (ds p) (es p) (zs p)) := by
  have hmark (l : Fin 2) (i : Fin N) :
      pairBranchMark N κ (coupledAuxVarianceFactor d₀ e₀ K₀)
          (fun p => coupledAuxVarianceFactor (ds p) (es p) (K p)) z₀ zs l i =
        pairBranchMark N κ K₀ K (coupledAuxMarksMap d₀ e₀ z₀)
          (fun p => coupledAuxMarksMap (ds p) (es p) (zs p)) l i := by
    unfold pairBranchMark
    rw [sum_coupledAuxVarianceFactor_mul_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    exact sum_coupledAuxVarianceFactor_mul_eq (ds p) (es p) (K p) (zs p) l i
  unfold pairHamG pairBranchZX pairBranchHamX
  simp_rw [hmark]

/-- The entire finite physical cascade is transported to auxiliary laws,
without positive-variance or covariance assumptions. -/
theorem cascadeRec_pairHamG_auxVarianceShare_eq {N κ : ℕ} (ns : Fin κ → ℝ)
    (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (d₀ e₀ : ℝ≥0) (ds es : Fin κ → ℝ≥0)
    (K₀ : Fin 2 → Fin 2 → ℝ) (K : Fin κ → Fin 2 → Fin 2 → ℝ)
    (z₀ : Fin N × (Fin 2 ⊕ Fin 2) → ℝ) :
    cascadeRec κ ns (siteGaussianMarks (Fin N × (Fin 2 ⊕ Fin 2)) κ (fun p => ds p + es p))
        (pairHamG N κ c H lam a (coupledAuxVarianceFactor d₀ e₀ K₀)
          (fun p => coupledAuxVarianceFactor (ds p) (es p) (K p)) z₀) =
      cascadeRec κ ns (siteGaussianMarks (Fin N × Fin 2) κ es)
        (pairHamG N κ c H lam a K₀ K (coupledAuxMarksMap d₀ e₀ z₀)) := by
  have hmap : (fun p => (siteGaussianMarks (Fin N × (Fin 2 ⊕ Fin 2)) κ
      (fun p => ds p + es p) p).map (coupledAuxMarksMap (ds p) (es p))) =
      siteGaussianMarks (Fin N × Fin 2) κ es := by
    funext p
    exact map_pi_gaussianReal_coupledAuxMarksMap (ds p) (es p)
  have he : pairHamG N κ c H lam a (coupledAuxVarianceFactor d₀ e₀ K₀)
        (fun p => coupledAuxVarianceFactor (ds p) (es p) (K p)) z₀ =
      fun zs => pairHamG N κ c H lam a K₀ K (coupledAuxMarksMap d₀ e₀ z₀)
        (fun p => coupledAuxMarksMap (ds p) (es p) (zs p)) := by
    funext zs
    exact pairHamG_auxVarianceShare_eq c H lam a d₀ e₀ ds es K₀ K z₀ zs
  rw [he, ← cascadeRec_map κ ns _ (fun p => coupledAuxMarksMap (ds p) (es p))
    (fun p => measurable_coupledAuxMarksMap (ds p) (es p))
    (measurable_pairHamG' N κ c H lam a K₀ K (coupledAuxMarksMap d₀ e₀ z₀))]
  simp only [hmap]

/-- Disorder and root averaging commute with the physical auxiliary
transport. No field moment hypothesis is needed for this law identity. -/
theorem integral_log_cascadeRec_pairHamG_auxVarianceShare_eq {N κ : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (Pm : Measure Ω) [IsProbabilityMeasure Pm]
    (ns : Fin κ → ℝ) (c : (Fin 2 → Config N) → ℝ) (Hf : Ω → EnergySpace N)
    (hHf : Measurable Hf) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (d₀ e₀ : ℝ≥0) (ds es : Fin κ → ℝ≥0)
    (K₀ : Fin 2 → Fin 2 → ℝ) (K : Fin κ → Fin 2 → Fin 2 → ℝ) :
    (∫ θ, Real.log (cascadeRec κ ns
        (siteGaussianMarks (Fin N × (Fin 2 ⊕ Fin 2)) κ (fun p => ds p + es p))
        (pairHamG N κ c (Hf θ.1) lam a (coupledAuxVarianceFactor d₀ e₀ K₀)
          (fun p => coupledAuxVarianceFactor (ds p) (es p) (K p)) θ.2)).toReal
        ∂Pm.prod (rootMarksLaw N (J := Fin 2 ⊕ Fin 2) (d₀ + e₀))) =
      ∫ θ, Real.log (cascadeRec κ ns (siteGaussianMarks (Fin N × Fin 2) κ es)
        (pairHamG N κ c (Hf θ.1) lam a K₀ K θ.2)).toReal
        ∂Pm.prod (rootMarksLaw N (J := Fin 2) e₀) := by
  let F := fun θ : Ω × (Fin N × Fin 2 → ℝ) => Real.log (cascadeRec κ ns
    (siteGaussianMarks (Fin N × Fin 2) κ es)
    (pairHamG N κ c (Hf θ.1) lam a K₀ K θ.2)).toReal
  have hFm : Measurable F :=
    (measurable_cascadeRec_prod κ ns (siteGaussianMarks (Fin N × Fin 2) κ es)
      (measurable_pairHamG_branchParam N κ c hHf lam a K₀ K)).ennreal_toReal.log
  have hmap : (Pm.prod (rootMarksLaw N (J := Fin 2 ⊕ Fin 2) (d₀ + e₀))).map
      (Prod.map id (coupledAuxMarksMap d₀ e₀)) =
      Pm.prod (rootMarksLaw N (J := Fin 2) e₀) := by
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_coupledAuxMarksMap d₀ e₀),
      Measure.map_id, map_pi_gaussianReal_coupledAuxMarksMap]
  have hi := integral_map (μ := Pm.prod (rootMarksLaw N (J := Fin 2 ⊕ Fin 2) (d₀ + e₀)))
    (measurable_id.prodMap (measurable_coupledAuxMarksMap d₀ e₀)).aemeasurable
    hFm.aestronglyMeasurable
  rw [hmap] at hi
  calc
    _ = ∫ θ, F (Prod.map id (coupledAuxMarksMap d₀ e₀) θ)
        ∂Pm.prod (rootMarksLaw N (J := Fin 2 ⊕ Fin 2) (d₀ + e₀)) := by
      apply integral_congr_ae (.of_forall fun θ => ?_)
      rw [cascadeRec_pairHamG_auxVarianceShare_eq]
      rfl
    _ = _ := hi.symm

/-- The matching split pressure after transport to its actual auxiliary
law. Inserted zero levels and the terminal mass-one level are still present. -/
noncomputable def parisiAuxSplitPressure {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t u : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (es : Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0)
    (a : Fin N × Fin 2 → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec ((p.val + 1) + ((k - p.val) + 1))
    (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p))
    (siteGaussianMarks (Fin N × Fin 2) ((p.val + 1) + ((k - p.val) + 1)) es)
    (pairHamG N _ (constraintR N u) (G₀.U θ.1) 0 a
      (couplingFactorSgn 1 (p.val + 2) 0)
      (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) θ.2)).toReal
    ∂Pm.prod (rootMarksLaw N (J := Fin 2) (parisiAuxRootVar ξ qs t))

/-- The physical endpoint in (14.311) has exactly the prescribed
auxiliary Gaussian law, with the same realized field in both replicas. -/
theorem parisiSplitPressure_eq_auxiliary {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (u : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (es : Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0)
    (a : Fin N × Fin 2 → ℝ) :
    parisiSplitPressure ξ ms qs p t u G₀ es a =
      parisiAuxSplitPressure ξ ms qs p t u G₀ es a := by
  have hi := integral_log_cascadeRec_pairHamG_auxVarianceShare_eq Pm
    (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p)) (constraintR N u)
    G₀.U G₀.measU 0 a (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
    (parisiDrivenSplitVars ξ qs p t u) es (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))
  rw [parisiDrivenRootVar_add_aux_eq ξ qs ht] at hi
  unfold parisiSplitPressure parisiAuxSplitPressure coupledG
  simp only [sub_self, Real.sqrt_zero, Real.sqrt_one, zero_smul, one_smul, zero_add]
  exact congrArg (fun x => (1 / (N : ℝ)) * x) hi

end SpinGlass
