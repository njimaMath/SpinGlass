import SpinGlass.Parisi.Coupled.CoupledPairGaussianRecursion

/-!
# The actual canonical positive site recursion

The proved Gaussian-column laws transport the standard-coordinate cascade
to the actual paired Gaussian marks. The full positive suffix is then
identified with its concrete paired Cole-Hopf list, with no supplied
recursion or covariance identity.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- Transport and identify the entire positive suffix of the actual
canonical one-site cascade for any separately unit-Lipschitz terminal. -/
theorem parisiRec_parisiCanonicalPositiveFactors_eq {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ)
    {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) (x y : ℝ) :
    parisiRec (parisiCanonicalPositivePieces ms r p).length
      (parisiCanonicalPositiveMasses ms r p)
      (siteGaussianMarks (ParisiCanonicalColumns ms r p) _ (fun _ => 1))
      (fun zs => F
        (x + ∑ i, ∑ j, (parisiCanonicalDrivenFactor ξ ms qs negative r p t u i +
          parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u i) 0 j * zs i j)
        (y + ∑ i, ∑ j, (parisiCanonicalDrivenFactor ξ ms qs negative r p t u i +
          parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u i) 1 j * zs i j)) =
      pairColeHopfIterate ((parisiCanonicalPositivePieces ms r p).map
        (ParisiCanonicalPiece.toPairLevel ξ ms qs negative r p t u)) F x y := by
  let κ := (parisiCanonicalPositivePieces ms r p).length
  let ps : Fin κ → PairColeHopfLevel := fun i =>
    ((parisiCanonicalPositivePieces ms r p)[i.val]).toPairLevel ξ ms qs negative r p t u
  let μstd := siteGaussianMarks (ParisiCanonicalColumns ms r p) κ (fun _ => 1)
  let μraw := siteGaussianMarks (Fin 2) κ (fun i => (ps i).variance)
  let φstd (i : Fin κ) (z : ParisiCanonicalColumns ms r p → ℝ) : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (fun l => ∑ j,
      (parisiCanonicalDrivenFactor ξ ms qs negative r p t u i +
        parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u i) l j * z j)
  let φraw (i : Fin κ) (z : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (fun l => ∑ j,
      ((parisiCanonicalPositivePieces ms r p)[i.val]).gaussianFactor negative r p l j * z j)
  let T (zs : Fin κ → EuclideanSpace ℝ (Fin 2)) : ℝ :=
    F (x + ∑ i, zs i 0) (y + ∑ i, zs i 1)
  have hT : Measurable T := (hF.continuous_uncurry.comp
    (show Continuous (fun zs : Fin κ → EuclideanSpace ℝ (Fin 2) =>
      (x + ∑ i, zs i 0, y + ∑ i, zs i 1)) by fun_prop)).measurable
  have hstd : ∀ i, Measurable (φstd i) := by intro i; dsimp only [φstd]; fun_prop
  have hraw : ∀ i, Measurable (φraw i) := by intro i; dsimp only [φraw]; fun_prop
  have hmap : (fun i => (μstd i).map (φstd i)) = fun i => (μraw i).map (φraw i) := by
    funext i
    exact map_gaussian_parisiCanonicalPositiveFactors_eq ξ ms qs negative r p t u i
  change parisiRec κ (fun i => (ps i).mass) μstd
    (fun zs => T (fun i => φstd i (zs i))) = _
  rw [← parisiRec_map κ (fun i => (ps i).mass) μstd φstd hstd hT,
    hmap, parisiRec_map κ (fun i => (ps i).mass) μraw φraw hraw hT]
  have hx (i : Fin κ) (z : Fin 2 → ℝ) :
      φraw i z 0 = (pairGaussianShift (ps i).kind z).1 := by
    change (∑ j, ((parisiCanonicalPositivePieces ms r p)[i.val]).gaussianFactor
      negative r p 0 j * z j) = _
    rw [pairGaussianShift_eq_factor]
    rfl
  have hy (i : Fin κ) (z : Fin 2 → ℝ) :
      φraw i z 1 = (pairGaussianShift (ps i).kind z).2 := by
    change (∑ j, ((parisiCanonicalPositivePieces ms r p)[i.val]).gaussianFactor
      negative r p 1 j * z j) = _
    rw [pairGaussianShift_eq_factor]
    rfl
  simp only [T, hx, hy]
  have hpos : ∀ i, 0 < (ps i).mass := parisiCanonicalPositiveMasses_pos ms hm r p
  have hl : List.ofFn ps = (parisiCanonicalPositivePieces ms r p).map
      (ParisiCanonicalPiece.toPairLevel ξ ms qs negative r p t u) :=
    List.ofFn_getElem_eq_map _ _
  simpa only [hl] using parisiRec_pairGaussian_comp_add_sum ps hpos hF x y

end SpinGlass
