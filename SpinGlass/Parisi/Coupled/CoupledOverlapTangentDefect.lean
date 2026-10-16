import SpinGlass.Parisi.Coupled.CoupledParisiSplitVariance
import Mathlib.Analysis.Convex.Continuous

/-!
# The terminal defect for a fixed trial overlap

Equation (14.147) allows the trial covariance and the realized constraint
to differ. Their exact discrepancy is the profile tangent defect.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable def parisiOverlapTangentDefect (ξ : ℝ → ℝ) (s u : ℝ) : ℝ :=
  ξ u - ξ s - (u - s) * deriv ξ s

theorem pairDiagDefect_overlapMatrix_eq (ξ : ℝ → ℝ) (s u : ℝ) :
    pairDiagDefect ξ u (fun l l' : Fin 2 => if l = l' then 1 else s) =
      parisiOverlapTangentDefect ξ s u := by
  simp [pairDiagDefect, parisiOverlapTangentDefect, Fin.sum_univ_two]
  ring

theorem parisiOverlapTangentDefect_timeProfile (ξ : ℝ → ℝ) (t s u : ℝ) :
    parisiOverlapTangentDefect (parisiTimeProfile ξ t) s u =
      t * parisiOverlapTangentDefect ξ s u := by
  simp only [parisiOverlapTangentDefect, parisiTimeProfile, deriv_parisiTimeProfile]
  ring

/-- The terminal split covariance at a fixed trial overlap contributes
its exact tangent defect at every realized overlap. -/
theorem pairDiagDefect_parisiSplitCouplingRho_trial (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (s u : ℝ) :
    pairDiagDefect ξ u (fun l l' => parisiSplitCouplingRho qs p s l l' (k + 3)) =
      parisiOverlapTangentDefect ξ s u := by
  have he : (fun l l' => parisiSplitCouplingRho qs p s l l' (k + 3)) =
      fun l l' => if l = l' then (1 : ℝ) else s := by
    funext l l'
    convert parisiSplitCouplingRho_top qs p s l l' using 1 <;> congr 1 <;> omega
  rw [he, pairDiagDefect_overlapMatrix_eq]

/-- Convexity makes the fixed-trial defect continuous in the realized
constraint, without requiring a derivative of the profile there. -/
theorem continuous_parisiOverlapTangentDefect
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) (s : ℝ) :
    Continuous (parisiOverlapTangentDefect ξ s) := by
  have hξc : Continuous ξ := continuousOn_univ.1 (hξ.convex.continuousOn isOpen_univ)
  exact (hξc.sub continuous_const).sub ((continuous_id.sub continuous_const).mul continuous_const)

end SpinGlass
