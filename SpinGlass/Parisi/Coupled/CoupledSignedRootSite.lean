import SpinGlass.Parisi.Coupled.CoupledIndependentPair
import SpinGlass.Parisi.Coupled.CoupledRootSignedResponse

/-!
# Independent branches under a signed driven root

The driven and auxiliary root factors are kept separate. Positive-level
marks have independent replica factors and transport to their total
variance law. The resulting conditional recursion is the two-field
recursion with its actual product-gradient coupling slope.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

/-- Independent positive-level factors can be mixed without changing
the arbitrary root factors or the two effective root fields. -/
theorem pairSiteF_varianceShare_independent_eq {n : ℕ} (ds es : Fin n → ℝ≥0)
    (L₀ : Fin 2 → Fin 2 ⊕ Fin 2 → ℝ) (lam : ℝ) (h : Fin 2 → ℝ)
    (z₀ : Fin 2 ⊕ Fin 2 → ℝ) (zs : Fin n → Fin 2 ⊕ Fin 2 → ℝ) :
    pairSiteF lam h L₀ (fun p =>
      coupledDrivenVarianceFactor (ds p) (es p) (fun l j => if l = j then 1 else 0) +
      coupledAuxVarianceFactor (ds p) (es p) (fun l j => if l = j then 1 else 0)) z₀ zs =
      independentPairSiteF lam (fun l => h l + ∑ j, L₀ l j * z₀ j)
        (fun p => coupledVarianceMixMap (ds p) (es p) (zs p)) := by
  have hmark (l : Fin 2) :
      pairSiteMark L₀ (fun p =>
        coupledDrivenVarianceFactor (ds p) (es p) (fun l j => if l = j then 1 else 0) +
        coupledAuxVarianceFactor (ds p) (es p) (fun l j => if l = j then 1 else 0)) z₀ zs l =
        (∑ j, L₀ l j * z₀ j) + ∑ p, coupledVarianceMixMap (ds p) (es p) (zs p) l := by
    unfold pairSiteMark
    simp_rw [sum_coupledVarianceFactors_mul_eq_mix]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  unfold independentPairSiteF pairSiteF
  rw [hmark 0, hmark 1, pairSiteMark_independent, pairSiteMark_independent]
  simp only [add_assoc]

/-- Transport of the actual conditional recursion, leaving the root
law and its two possibly different effective fields unchanged. -/
theorem parisiRec_pairSiteF_varianceShare_independent_eq {n : ℕ}
    (ns : Fin n → ℝ) (ds es : Fin n → ℝ≥0)
    (L₀ : Fin 2 → Fin 2 ⊕ Fin 2 → ℝ) (lam : ℝ) (h : Fin 2 → ℝ)
    (z₀ : Fin 2 ⊕ Fin 2 → ℝ) :
    parisiRec n ns (siteGaussianMarks (Fin 2 ⊕ Fin 2) n (fun p => ds p + es p))
      (pairSiteF lam h L₀ (fun p =>
        coupledDrivenVarianceFactor (ds p) (es p) (fun l j => if l = j then 1 else 0) +
        coupledAuxVarianceFactor (ds p) (es p) (fun l j => if l = j then 1 else 0)) z₀) =
      independentPairSiteRec ns (fun p => ds p + es p) lam
        (fun l => h l + ∑ j, L₀ l j * z₀ j) := by
  have hmap : (fun p => (siteGaussianMarks (Fin 2 ⊕ Fin 2) n (fun p => ds p + es p) p).map
      (coupledVarianceMixMap (ds p) (es p))) = siteGaussianMarks (Fin 2) n (fun p => ds p + es p) := by
    funext p
    exact map_pi_gaussianReal_coupledVarianceMixMap (ds p) (es p)
  have hpoint : pairSiteF lam h L₀ (fun p =>
      coupledDrivenVarianceFactor (ds p) (es p) (fun l j => if l = j then 1 else 0) +
      coupledAuxVarianceFactor (ds p) (es p) (fun l j => if l = j then 1 else 0)) z₀ =
      fun zs => independentPairSiteF lam (fun l => h l + ∑ j, L₀ l j * z₀ j)
        (fun p => coupledVarianceMixMap (ds p) (es p) (zs p)) := by
    funext zs
    exact pairSiteF_varianceShare_independent_eq ds es L₀ lam h z₀ zs
  rw [hpoint]
  unfold independentPairSiteF
  rw [← parisiRec_map n ns _ (fun p => coupledVarianceMixMap (ds p) (es p))
    (fun p => measurable_coupledVarianceMixMap (ds p) (es p))
    (measurable_pairSiteF' lam (fun l => h l + ∑ j, L₀ l j * z₀ j) 0
      (fun _ l j => if l = j then 1 else 0) 0), hmap]
  rfl

/-- The full one-site average is the actual two-field conditional
recursion integrated against the original root marks. -/
theorem pairSiteY₀_varianceShare_independent_eq {n : ℕ}
    (ns : Fin n → ℝ) (v₀ : ℝ≥0) (ds es : Fin n → ℝ≥0)
    (L₀ : Fin 2 → Fin 2 ⊕ Fin 2 → ℝ) (lam : ℝ) (h : Fin 2 → ℝ) :
    pairSiteY₀ ns v₀ (fun p => ds p + es p) lam h L₀ (fun p =>
      coupledDrivenVarianceFactor (ds p) (es p) (fun l j => if l = j then 1 else 0) +
      coupledAuxVarianceFactor (ds p) (es p) (fun l j => if l = j then 1 else 0)) =
      ∫ z₀, independentPairSiteRec ns (fun p => ds p + es p) lam
        (fun l => h l + ∑ j, L₀ l j * z₀ j)
        ∂Measure.pi (fun _ : Fin 2 ⊕ Fin 2 => gaussianReal 0 v₀) := by
  unfold pairSiteY₀
  exact integral_congr_ae (.of_forall fun z₀ =>
    parisiRec_pairSiteF_varianceShare_independent_eq ns ds es L₀ lam h z₀)

theorem measurable_independentPairSiteRec {n : ℕ} (ns : Fin n → ℝ)
    (vs : Fin n → ℝ≥0) (lam : ℝ) : Measurable (independentPairSiteRec ns vs lam) := by
  have hG : Measurable (Function.uncurry fun (x : Fin 2 → ℝ) (ys : Fin n → Fin 2 → ℝ) =>
      ENNReal.ofReal (Real.exp (independentPairSiteF lam x ys))) := by
    unfold independentPairSiteF pairSiteF pairSiteMark pairSiteY
    fun_prop
  exact (measurable_cascadeRec_prod n ns (siteGaussianMarks (Fin 2) n vs) hG).ennreal_toReal.log

/-- The conditional two-field recursion is one-Lipschitz in coupling,
uniformly in both root fields. -/
theorem abs_independentPairSiteRec_sub_le {n : ℕ} (ns : Fin n → ℝ) (vs : Fin n → ℝ≥0)
    (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1) (x : Fin 2 → ℝ) (a b : ℝ) :
    |independentPairSiteRec ns vs a x - independentPairSiteRec ns vs b x| ≤ |a - b| := by
  have hY (l : ℝ) : pairSiteY₀ ns 0 vs l x (0 : Fin 2 → Fin 2 → ℝ)
      (fun _ l j => if l = j then 1 else 0) = independentPairSiteRec ns vs l x := by
    unfold pairSiteY₀
    rw [pi_gaussianReal_zero_eq_dirac, integral_dirac]
    rfl
  have hd (l : ℝ) := hasDerivAt_pairSiteY₀ ns hpos hle 0 vs l x
    (0 : Fin 2 → Fin 2 → ℝ) (fun _ l j => if l = j then 1 else 0)
  have hh := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun l => pairSiteY₀ ns 0 vs l x (0 : Fin 2 → Fin 2 → ℝ)
      (fun _ l j => if l = j then 1 else 0))
    (f' := fun l => pairSiteY₀' ns 0 vs l x (0 : Fin 2 → Fin 2 → ℝ)
      (fun _ l j => if l = j then 1 else 0)) (C := (1 : ℝ))
    (fun l _ => (hd l).hasDerivWithinAt)
    (fun l _ => by rw [Real.norm_eq_abs]; exact abs_pairSiteY₀'_le_one ns hpos hle 0 vs l x 0 _)
    (mem_univ b) (mem_univ a)
  simpa only [hY, Real.norm_eq_abs, one_mul] using hh

/-- Differentiation of the actual two-field conditional recursion
under any probability root/field law, with envelope one. -/
theorem hasDerivAt_integral_independentPairSiteRec_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (ns : Fin n → ℝ) (vs : Fin n → ℝ≥0)
    (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1) {H : Ω → Fin 2 → ℝ}
    (hH : Measurable H) (hi : Integrable (fun ω => independentPairSiteRec ns vs 0 (H ω)) μ) :
    HasDerivAt (fun lam => ∫ ω, independentPairSiteRec ns vs lam (H ω) ∂μ)
      (∫ ω, deriv (coleHopfIterate n ns vs (parisiLogCoshTerminal 0)) (H ω 0) *
        deriv (coleHopfIterate n ns vs (parisiLogCoshTerminal 0)) (H ω 1) ∂μ) 0 := by
  refine (hasDerivAt_integral_of_dominated_loc_of_lip (s := univ) (bound := fun _ => (1 : ℝ))
    (by simp) (.of_forall fun lam => ((measurable_independentPairSiteRec ns vs lam).comp hH).aestronglyMeasurable)
    hi (((measurable_deriv (coleHopfIterate n ns vs (parisiLogCoshTerminal 0))).comp
      ((measurable_pi_apply 0).comp hH)).mul
      ((measurable_deriv (coleHopfIterate n ns vs (parisiLogCoshTerminal 0))).comp
        ((measurable_pi_apply 1).comp hH))).aestronglyMeasurable
    ?_ (integrable_const 1)
    (.of_forall fun ω => hasDerivAt_independentPairSiteRec_zero ns vs hpos hle (H ω))).2
  exact .of_forall fun ω => by
    have hL : ∀ a b, |independentPairSiteRec ns vs b (H ω) - independentPairSiteRec ns vs a (H ω)| ≤
        1 * |b - a| := fun a b => by
      simpa only [one_mul] using abs_independentPairSiteRec_sub_le ns vs hpos hle (H ω) b a
    have hnn : Real.nnabs (1 : ℝ) = 1 := by norm_num
    simpa only [hnn, Real.toNNReal_one, Function.comp_apply] using
      (lipschitzWith_toNNReal_of_abs_sub_le hL).lipschitzOnWith (s := univ)

end SpinGlass
