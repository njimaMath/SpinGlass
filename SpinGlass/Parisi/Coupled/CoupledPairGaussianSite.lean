import SpinGlass.Parisi.Coupled.CoupledPairGaussianRecursion
import SpinGlass.Parisi.Coupled.CoupledPairTerminal

/-!
# The actual two-column Gaussian site value as a paired list

The positive Gaussian cascade is followed by its genuine mass-zero root
expectation. All three root and level kinds use their actual two-column
Gaussian law. This supplies the original auxiliary site recursion at time
zero, without a scalar slope or recursion identity supplied as a hypothesis.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- The full actual Gaussian site recursion equals its paired list
at any coupling, including a zero-mass root expectation. -/
theorem pairSiteY₀_pairGaussian_eq {k : ℕ}
    (q : PairColeHopfLevel) (hq : q.mass = 0) (ps : Fin k → PairColeHopfLevel)
    (hpos : ∀ i, 0 < (ps i).mass) (lam : ℝ) (h : Fin 2 → ℝ) :
    pairSiteY₀ (fun i => (ps i).mass) q.variance (fun i => (ps i).variance) lam h
      q.kind.gaussianFactor (fun i => (ps i).kind.gaussianFactor) =
      pairColeHopfIterate (q :: List.ofFn ps) (pairSiteY lam) (h 0) (h 1) := by
  let F := pairSiteY lam
  let A := pairColeHopfIterate (List.ofFn ps) F
  have hF : PairUnitLipschitz F := pairUnitLipschitz_pairSiteY lam
  have hA : PairUnitLipschitz A := pairColeHopfIterate_lipschitz _ hF
  have hp (z₀ : Fin 2 → ℝ) : parisiRec k (fun i => (ps i).mass)
      (siteGaussianMarks (Fin 2) k (fun i => (ps i).variance))
      (pairSiteF lam h q.kind.gaussianFactor (fun i => (ps i).kind.gaussianFactor) z₀) =
      A (h 0 + (pairGaussianShift q.kind z₀).1)
        (h 1 + (pairGaussianShift q.kind z₀).2) := by
    have he : pairSiteF lam h q.kind.gaussianFactor (fun i => (ps i).kind.gaussianFactor) z₀ =
        fun zs => F ((h 0 + (pairGaussianShift q.kind z₀).1) +
            ∑ i, (pairGaussianShift (ps i).kind (zs i)).1)
          ((h 1 + (pairGaussianShift q.kind z₀).2) +
            ∑ i, (pairGaussianShift (ps i).kind (zs i)).2) := by
      funext zs
      simp only [pairSiteF, pairSiteMark, pairGaussianShift_eq_factor, F, add_assoc]
    rw [he]
    exact parisiRec_pairGaussian_comp_add_sum ps hpos hF _ _
  unfold pairSiteY₀
  simp_rw [hp]
  exact (pairColeHopfOperator_zero_eq_gaussian_integral hA q hq (h 0) (h 1)).symm

end SpinGlass
