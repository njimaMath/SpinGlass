import SpinGlass.Parisi.Coupled.CoupledPairGaussianSite

/-!
# Continuity of the actual coupled Gaussian site law

The original common-prefix and independent-suffix two-column site value
is a concrete paired list at every coupling. Its actual field average is
continuous under continuous root and positive variance families, with a
finite first field moment. Fixed-mass comparison trials can therefore be
held fixed while time and the realized overlap vary.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

def pairCouplingKind (τ p : ℕ) : PairColeHopfKind :=
  if p < τ then .common else .independent

theorem pairCouplingKind_gaussianFactor (τ p : ℕ) :
    (pairCouplingKind τ p).gaussianFactor = couplingFactorSgn 1 τ p := by
  by_cases hp : p < τ <;>
    simp [pairCouplingKind, hp, PairColeHopfKind.gaussianFactor, couplingFactorSgn]

/-- The actual common-prefix site law equals a full paired list,
including its genuine root expectation, at every fixed coupling. -/
theorem randomFieldPairSiteY₀_eq_pairCouplingList {k : ℕ}
    (μh : Measure ℝ) (ns : Fin k → ℝ) (hpos : ∀ i, 0 < ns i)
    (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (τ : ℕ) (lam : ℝ) :
    randomFieldPairSiteY₀ μh ns v₀ vs lam (couplingFactorSgn 1 τ 0)
      (fun i => couplingFactorSgn 1 τ (i.val + 1)) =
      randomFieldPairColeHopfTerminalValue μh
        (⟨0, v₀, pairCouplingKind τ 0⟩ ::
          List.ofFn (fun i => ⟨ns i, vs i, pairCouplingKind τ (i.val + 1)⟩)) (pairSiteY lam) := by
  unfold randomFieldPairSiteY₀ randomFieldPairColeHopfTerminalValue
  apply integral_congr_ae (.of_forall fun h => ?_)
  simpa only [pairCouplingKind_gaussianFactor] using
    pairSiteY₀_pairGaussian_eq ⟨0, v₀, pairCouplingKind τ 0⟩ rfl
      (fun i => ⟨ns i, vs i, pairCouplingKind τ (i.val + 1)⟩) hpos lam (fun _ => h)

/-- The field average of the actual two-column Gaussian site value is
continuous in its continuous root and positive variances at any coupling.
No variance positivity or exponential field moment is needed. -/
theorem continuous_randomFieldPairSiteY₀_of_continuous_variance
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {X : Type*} [TopologicalSpace X] {k : ℕ}
    (ns : Fin k → ℝ) (hpos : ∀ i, 0 < ns i) (τ : ℕ) (lam : ℝ)
    (v₀ : X → ℝ≥0) (vs : X → Fin k → ℝ≥0)
    (hv₀ : Continuous v₀) (hvs : ∀ i, Continuous (fun x => vs x i)) :
    Continuous (fun x => randomFieldPairSiteY₀ μh ns (v₀ x) (vs x) lam
      (couplingFactorSgn 1 τ 0) (fun i => couplingFactorSgn 1 τ (i.val + 1))) := by
  let l : List (Fin (k + 1)) := List.ofFn id
  let mass : Fin (k + 1) → ℝ := Fin.cons 0 ns
  let kind : Fin (k + 1) → PairColeHopfKind := fun i => pairCouplingKind τ i.val
  let variance (x : X) : Fin (k + 1) → ℝ≥0 := Fin.cons (v₀ x) (vs x)
  have hvar (i : Fin (k + 1)) : Continuous (fun x => variance x i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [variance, Fin.cons_zero] using hv₀
    · simpa only [variance, Fin.cons_succ] using hvs j
  have hc := continuous_randomFieldPairColeHopfTerminalValue_of_continuous_variance hμ
    l mass kind variance hvar (pairUnitLipschitz_pairSiteY lam)
  have he (x : X) : randomFieldPairSiteY₀ μh ns (v₀ x) (vs x) lam
      (couplingFactorSgn 1 τ 0) (fun i => couplingFactorSgn 1 τ (i.val + 1)) =
      randomFieldPairColeHopfTerminalValue μh
        (l.map (fun i => ⟨mass i, variance x i, kind i⟩)) (pairSiteY lam) := by
    rw [randomFieldPairSiteY₀_eq_pairCouplingList μh ns hpos]
    congr 1
    simp only [l, List.map_ofFn]
    rw [List.ofFn_succ]
    rfl
  exact hc.congr (fun x => (he x).symm)

end SpinGlass
