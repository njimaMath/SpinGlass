/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.ParisiFunctional

/-!
# Quenched random external fields

This file records the law of the i.i.d. site variables in Talagrand, *Mean Field Models for Spin
Glasses*, Vol. II, Chapter 14.  The external field is kept separate from the Gaussian interaction
and cascade marks.  In particular, all replicas of one quenched system use the same point of
`Fin N → ℝ` sampled from `externalFieldVecLaw`.
-/

open MeasureTheory ProbabilityTheory

namespace SpinGlass

noncomputable section

/-- The product law of the i.i.d. quenched external fields `(hᵢ)_{i ≤ N}`. -/
def externalFieldVecLaw (N : ℕ) (μh : Measure ℝ) : Measure (Fin N → ℝ) :=
  Measure.pi fun _ : Fin N => μh

instance (N : ℕ) (μh : Measure ℝ) [IsProbabilityMeasure μh] :
    IsProbabilityMeasure (externalFieldVecLaw N μh) := by
  unfold externalFieldVecLaw
  infer_instance

/-- Every coordinate of the i.i.d. external-field vector has law `μh`. -/
lemma measurePreserving_externalFieldVec_apply (N : ℕ) (μh : Measure ℝ)
  [IsProbabilityMeasure μh] (i : Fin N) :
    MeasurePreserving (Function.eval i) (externalFieldVecLaw N μh) μh := by
  exact measurePreserving_eval (μ := fun _ : Fin N => μh) i

/-- Integration of a one-coordinate observable reduces to integration against the site law. -/
lemma integral_externalFieldVec_apply (N : ℕ) (μh : Measure ℝ) [IsProbabilityMeasure μh]
    (i : Fin N) (f : ℝ → ℝ) (hf : AEStronglyMeasurable f μh) :
    ∫ hVec, f (hVec i) ∂externalFieldVecLaw N μh = ∫ h, f h ∂μh := by
  let P := externalFieldVecLaw N μh
  have hmap : P.map (Function.eval i) = μh :=
    (measurePreserving_externalFieldVec_apply N μh i).map_eq
  have hf' : AEStronglyMeasurable f (P.map (Function.eval i)) := by
    rw [hmap]
    exact hf
  calc
    ∫ hVec, f (hVec i) ∂P = ∫ h, f h ∂P.map (Function.eval i) :=
      (integral_map (measurable_pi_apply i).aemeasurable hf').symm
    _ = ∫ h, f h ∂μh := by rw [hmap]

end

end SpinGlass
