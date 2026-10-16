import SpinGlass.Parisi.Coupled.CoupledCanonicalRootRecursion
import SpinGlass.Parisi.Coupled.CoupledCanonicalContinuity
import SpinGlass.Parisi.Coupled.CoupledPairTerminal

/-!
# The complete canonical site recursion at arbitrary coupling

The actual positive cascade and every zero-mass root expectation are
identified for an arbitrary separately unit-Lipschitz terminal. Applying
this to the actual coupled terminal gives the concrete one-site value
and its joint time/magnitude continuity at every fixed coupling.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- The concrete full canonical Gaussian recursion equals the paired
list for any separately unit-Lipschitz terminal, including every root
expectation of a split root. -/
theorem integral_parisiCanonicalRec_terminal_eq {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ)
    {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) (x y : ℝ) :
    (∫ z₀ : ParisiCanonicalColumns ms r p → ℝ,
      parisiRec (parisiCanonicalPositivePieces ms r p).length
        (parisiCanonicalPositiveMasses ms r p)
        (siteGaussianMarks (ParisiCanonicalColumns ms r p) _ (fun _ => 1))
        (fun zs => F
          ((x + ∑ j, (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u +
            parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u) 0 j * z₀ j) +
            ∑ i, ∑ j, (parisiCanonicalDrivenFactor ξ ms qs negative r p t u i +
              parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u i) 0 j * zs i j)
          ((y + ∑ j, (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u +
            parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u) 1 j * z₀ j) +
            ∑ i, ∑ j, (parisiCanonicalDrivenFactor ξ ms qs negative r p t u i +
              parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u i) 1 j * zs i j))
      ∂Measure.pi (fun _ : ParisiCanonicalColumns ms r p => gaussianReal 0 1)) =
      pairColeHopfIterate (parisiCanonicalPairLevels ξ ms qs negative r p t u) F x y := by
  let A := pairColeHopfIterate ((parisiCanonicalPositivePieces ms r p).map
    (ParisiCanonicalPiece.toPairLevel ξ ms qs negative r p t u)) F
  have hA : PairUnitLipschitz A := pairColeHopfIterate_lipschitz _ hF
  simp_rw [parisiRec_parisiCanonicalPositiveFactors_eq ξ ms qs hm negative r p t u hF]
  rw [integral_parisiCanonicalRootFactors_eq ξ ms qs negative r p t u hA x y]
  change pairColeHopfIterate ((parisiCanonicalRootPieces ms r p).map
      (ParisiCanonicalPiece.toPairLevel ξ ms qs negative r p t u))
    (pairColeHopfIterate ((parisiCanonicalPositivePieces ms r p).map
      (ParisiCanonicalPiece.toPairLevel ξ ms qs negative r p t u)) F) x y = _
  rw [← pairColeHopfIterate_append, ← List.map_append, parisiCanonicalRoot_append_positive]
  rfl

/-- The actual standard-column site value at any coupling is the
complete canonical paired list applied to the actual terminal (14.144). -/
theorem pairSiteY₀_parisiCanonical_eq {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u lam : ℝ) (h : Fin 2 → ℝ) :
    pairSiteY₀ (parisiCanonicalPositiveMasses ms r p) 1 (fun _ => 1) lam h
      (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u +
        parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u)
      (fun i => parisiCanonicalDrivenFactor ξ ms qs negative r p t u i +
        parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u i) =
      pairColeHopfIterate (parisiCanonicalPairLevels ξ ms qs negative r p t u)
        (pairSiteY lam) (h 0) (h 1) := by
  unfold pairSiteY₀ pairSiteF pairSiteMark
  simp only [← add_assoc]
  exact integral_parisiCanonicalRec_terminal_eq ξ ms qs hm negative r p t u
    (pairUnitLipschitz_pairSiteY lam) (h 0) (h 1)

noncomputable def parisiCanonicalSiteValue (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u lam : ℝ) : ℝ :=
  randomFieldPairColeHopfTerminalValue μh
    (parisiCanonicalPairLevels ξ ms qs negative r p t u) (pairSiteY lam)

theorem parisiCanonicalSiteValue_zero_eq (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) :
    parisiCanonicalSiteValue μh ξ ms qs negative r p t u 0 =
      randomFieldPairColeHopfListValue μh (parisiCanonicalPairLevels ξ ms qs negative r p t u) := by
  unfold parisiCanonicalSiteValue randomFieldPairColeHopfTerminalValue
    randomFieldPairColeHopfListValue
  have he : pairSiteY 0 = fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b := by
    funext a b
    simp only [pairSiteY_zero, parisiLogCoshTerminal, zero_add]
  rw [he]

theorem randomFieldPairSiteY₀_parisiCanonical_eq {k : ℕ}
    (μh : Measure ℝ) (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u lam : ℝ) :
    randomFieldPairSiteY₀ μh (parisiCanonicalPositiveMasses ms r p) 1 (fun _ => 1) lam
      (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u +
        parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u)
      (fun i => parisiCanonicalDrivenFactor ξ ms qs negative r p t u i +
        parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u i) =
      parisiCanonicalSiteValue μh ξ ms qs negative r p t u lam := by
  unfold randomFieldPairSiteY₀ parisiCanonicalSiteValue randomFieldPairColeHopfTerminalValue
  exact integral_congr_ae (.of_forall fun h =>
    pairSiteY₀_parisiCanonical_eq ξ ms qs hm negative r p t u lam (fun _ => h))

theorem continuousOn_parisiCanonicalSiteValue_time_overlap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (lam : ℝ) :
    ContinuousOn (fun x : ℝ × ℝ => parisiCanonicalSiteValue μh ξ ms qs negative r p x.1 x.2 lam)
      (univ ×ˢ Icc (0 : ℝ) 1) := by
  apply continuousOn_iff_continuous_domRestrict.2
  exact continuous_randomFieldPairColeHopfTerminalValue_of_continuous_variance
    (X := (univ ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ))) hμ
    (parisiCanonicalMergedPieces ms r p) (ParisiCanonicalPiece.physicalMass ms r p)
    (ParisiCanonicalPiece.kind negative r p)
    (fun x e => e.variance ξ qs p x.val.1 x.val.2)
    (fun e => (continuousOn_parisiCanonicalPiece_variance_time_overlap hξ qs p e).domRestrict)
    (pairUnitLipschitz_pairSiteY lam)

end SpinGlass
