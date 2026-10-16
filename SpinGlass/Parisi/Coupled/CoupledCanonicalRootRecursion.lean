import SpinGlass.Parisi.Coupled.CoupledCanonicalSiteRecursion
import SpinGlass.Parisi.Coupled.CoupledPairGaussianExpectation
import SpinGlass.Parisi.Coupled.CoupledLambdaZero

/-!
# The complete canonical one-site recursion with its zero-mass root

The actual aggregate root law is transported to its finite product of
Gaussian marks. Its zero-mass expectations are identified by integrability
and Fubini, then combined with the proved positive suffix. This gives the
complete canonical one-site value used in Proposition 14.8.6.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- The actual standard-coordinate aggregate root expectation equals
the full zero-mass paired root iterate, including a split-root third mark. -/
theorem integral_parisiCanonicalRootFactors_eq {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ)
    {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) (x y : ℝ) :
    (∫ z : ParisiCanonicalColumns ms r p → ℝ,
      F (x + ∑ j, (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u +
          parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u) 0 j * z j)
        (y + ∑ j, (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u +
          parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u) 1 j * z j)
      ∂Measure.pi (fun _ : ParisiCanonicalColumns ms r p => gaussianReal 0 1)) =
      pairColeHopfIterate ((parisiCanonicalRootPieces ms r p).map
        (ParisiCanonicalPiece.toPairLevel ξ ms qs negative r p t u)) F x y := by
  let R := (parisiCanonicalRootPieces ms r p).length
  let ps : Fin R → PairColeHopfLevel := fun i =>
    ((parisiCanonicalRootPieces ms r p)[i.val]).toPairLevel ξ ms qs negative r p t u
  let μstd := Measure.pi (fun _ : ParisiCanonicalColumns ms r p => gaussianReal 0 1)
  let μraw := Measure.pi (fun j : Fin R × Fin 2 => gaussianReal 0 (ps j.1).variance)
  let φstd (z : ParisiCanonicalColumns ms r p → ℝ) : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (fun l => ∑ j,
      (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u +
        parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u) l j * z j)
  let φraw (z : Fin R × Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (fun l => ∑ j, (ps j.1).kind.gaussianFactor l j.2 * z j)
  let T (z : EuclideanSpace ℝ (Fin 2)) := F (x + z 0) (y + z 1)
  have hT : Measurable T := (hF.continuous_uncurry.comp
    (show Continuous (fun z : EuclideanSpace ℝ (Fin 2) => (x + z 0, y + z 1)) by
      fun_prop)).measurable
  have hstd : Measurable φstd := by dsimp only [φstd]; fun_prop
  have hraw : Measurable φraw := by dsimp only [φraw]; fun_prop
  have hmap : μstd.map φstd = μraw.map φraw :=
    map_gaussian_parisiCanonicalRootFactors_eq ξ ms qs negative r p t u
  have hzero : ∀ i, (ps i).mass = 0 := fun i =>
    parisiCanonicalRootPieces_mass_zero ms r p _ (List.getElem_mem _)
  have hl : List.ofFn ps = (parisiCanonicalRootPieces ms r p).map
      (ParisiCanonicalPiece.toPairLevel ξ ms qs negative r p t u) :=
    List.ofFn_getElem_eq_map _ _
  change (∫ z, T (φstd z) ∂μstd) = _
  calc
    _ = ∫ z, T z ∂μstd.map φstd := (integral_map hstd.aemeasurable hT.aestronglyMeasurable).symm
    _ = ∫ z, T z ∂μraw.map φraw := by rw [hmap]
    _ = ∫ z, T (φraw z) ∂μraw := integral_map hraw.aemeasurable hT.aestronglyMeasurable
    _ = _ := by
      simpa only [T, φraw, μraw, hl] using
        integral_pairGaussian_flat_comp_add_sum_mass_zero ps hzero hF x y

/-- At coupling zero, the concrete standard-coordinate site recursion
is exactly the complete canonical paired list. Both its positive suffix
and all zero-mass root expectations are proved identifications. -/
theorem pairSiteY₀_parisiCanonical_zero_eq {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u h : ℝ) :
    pairSiteY₀ (parisiCanonicalPositiveMasses ms r p) 1 (fun _ => 1) 0 (fun _ => h)
      (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u +
        parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u)
      (fun i => parisiCanonicalDrivenFactor ξ ms qs negative r p t u i +
        parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u i) =
      pairColeHopfIterate (parisiCanonicalPairLevels ξ ms qs negative r p t u)
        (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) h h := by
  let F := fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b
  have hF : PairUnitLipschitz F := pairUnitLipschitz_sum (abs_parisiLogCoshTerminal_sub_le 0)
  let K₀ := parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u +
    parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u
  let K := fun i => parisiCanonicalDrivenFactor ξ ms qs negative r p t u i +
    parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u i
  let A := pairColeHopfIterate ((parisiCanonicalPositivePieces ms r p).map
    (ParisiCanonicalPiece.toPairLevel ξ ms qs negative r p t u)) F
  have hA : PairUnitLipschitz A := pairColeHopfIterate_lipschitz _ hF
  have hpoint (z₀ : ParisiCanonicalColumns ms r p → ℝ) :
      parisiRec (parisiCanonicalPositivePieces ms r p).length
        (parisiCanonicalPositiveMasses ms r p)
        (siteGaussianMarks (ParisiCanonicalColumns ms r p) _ (fun _ => 1))
        (pairSiteF 0 (fun _ => h) K₀ K z₀) =
      A (h + ∑ j, K₀ 0 j * z₀ j) (h + ∑ j, K₀ 1 j * z₀ j) := by
    have he : pairSiteF 0 (fun _ => h) K₀ K z₀ =
        fun zs => F ((h + ∑ j, K₀ 0 j * z₀ j) + ∑ i, ∑ j, K i 0 j * zs i j)
          ((h + ∑ j, K₀ 1 j * z₀ j) + ∑ i, ∑ j, K i 1 j * zs i j) := by
      funext zs
      simp only [pairSiteF, pairSiteMark, pairSiteY_zero, F, parisiLogCoshTerminal,
        zero_add, add_assoc]
    rw [he]
    exact parisiRec_parisiCanonicalPositiveFactors_eq ξ ms qs hm negative r p t u hF _ _
  unfold pairSiteY₀
  change (∫ z₀, parisiRec _ _ _ (pairSiteF 0 (fun _ => h) K₀ K z₀)
    ∂Measure.pi (fun _ : ParisiCanonicalColumns ms r p => gaussianReal 0 1)) = _
  simp_rw [hpoint]
  rw [integral_parisiCanonicalRootFactors_eq ξ ms qs negative r p t u hA h h]
  change pairColeHopfIterate ((parisiCanonicalRootPieces ms r p).map
      (ParisiCanonicalPiece.toPairLevel ξ ms qs negative r p t u))
    (pairColeHopfIterate ((parisiCanonicalPositivePieces ms r p).map
      (ParisiCanonicalPiece.toPairLevel ξ ms qs negative r p t u)) F) h h = _
  rw [← pairColeHopfIterate_append, ← List.map_append, parisiCanonicalRoot_append_positive]
  rfl

/-- The field-averaged concrete site value is the actual full paired
list value. This is an identity for any field measure; later estimates
retain their probability and first-moment assumptions. -/
theorem randomFieldPairSiteY₀_parisiCanonical_zero_eq {k : ℕ}
    (μh : Measure ℝ) (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) :
    randomFieldPairSiteY₀ μh (parisiCanonicalPositiveMasses ms r p) 1 (fun _ => 1) 0
      (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u +
        parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u)
      (fun i => parisiCanonicalDrivenFactor ξ ms qs negative r p t u i +
        parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u i) =
      randomFieldPairColeHopfListValue μh (parisiCanonicalPairLevels ξ ms qs negative r p t u) := by
  unfold randomFieldPairSiteY₀ randomFieldPairColeHopfListValue
  exact integral_congr_ae (.of_forall fun h =>
    pairSiteY₀_parisiCanonical_zero_eq ξ ms qs hm negative r p t u h)

end SpinGlass
