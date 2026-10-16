import SpinGlass.Parisi.Coupled.CoupledCanonicalPieces
import SpinGlass.Parisi.Coupled.CoupledPairVarianceContinuity

/-!
# Continuity of the concrete canonical one-site value

At fixed original masses, the physical ordering and layer kinds are fixed.
Every actual variance is continuous in time and magnitude, including its
clamped zero values. The paired variance modulus therefore supplies the
field-averaged continuity needed for the compact pressure-gap argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- The actual labelled variance, with its prescribed clamping, is
continuous in time and magnitude on the profile interval. -/
theorem continuousOn_parisiCanonicalPiece_variance_time_overlap
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 2)) (e : ParisiCanonicalPiece k) :
    ContinuousOn (fun x : ℝ × ℝ => e.variance ξ qs p x.1 x.2)
      (univ ×ˢ Icc (0 : ℝ) 1) := by
  have hmaps : MapsTo (Prod.snd : ℝ × ℝ → ℝ)
      (univ ×ˢ Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := fun _ hx => hx.2
  have hd := hξ.deriv_continuous.comp continuous_snd.continuousOn hmaps
  have ht : Continuous (fun x : ℝ × ℝ => x.1.toNNReal) :=
    continuous_real_toNNReal.comp continuous_fst
  cases e with
  | auxiliary i =>
    exact ((continuous_real_toNNReal.comp (continuous_const.sub continuous_fst)).mul
      continuous_const).continuousOn
  | driven i =>
    by_cases hi : i = p
    · simp only [ParisiCanonicalPiece.variance, hi, ite_true]
      exact ht.continuousOn.mul
        (continuous_real_toNNReal.comp_continuousOn (hd.sub continuousOn_const))
    · simp only [ParisiCanonicalPiece.variance, hi, ite_false]
      exact (ht.mul continuous_const).continuousOn
  | splitRight =>
    exact ht.continuousOn.mul
      (continuous_real_toNNReal.comp_continuousOn (continuousOn_const.sub hd))

/-- The concrete canonical paired one-site value is jointly continuous
on the full closed magnitude interval, at every fixed original mass array.
Only a probability field law and a finite first moment are used. -/
theorem continuousOn_randomFieldPairColeHopfListValue_parisiCanonical
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    ContinuousOn (fun x : ℝ × ℝ => randomFieldPairColeHopfListValue μh
      (parisiCanonicalPairLevels ξ ms qs negative r p x.1 x.2))
      (univ ×ˢ Icc (0 : ℝ) 1) := by
  apply continuousOn_iff_continuous_domRestrict.2
  exact continuous_randomFieldPairColeHopfListValue_of_continuous_variance
    (X := (univ ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ))) hμ
    (parisiCanonicalMergedPieces ms r p) (ParisiCanonicalPiece.physicalMass ms r p)
    (ParisiCanonicalPiece.kind negative r p)
    (fun x e => e.variance ξ qs p x.val.1 x.val.2)
    (fun e => (continuousOn_parisiCanonicalPiece_variance_time_overlap hξ qs p e).domRestrict)

end SpinGlass
