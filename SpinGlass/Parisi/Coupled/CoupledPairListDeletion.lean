import SpinGlass.Parisi.Coupled.CoupledPairRecursion

/-!
# Deleting zero-variance paired Gaussian layers

Every paired layer with variance zero is the identity, including its
mass-zero expectation branch. All such layers can be filtered from a
finite list without changing the actual recursion or its terminal.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

theorem pairColeHopfOperator_zero_variance_eq (p : PairColeHopfLevel) (hp : p.variance = 0)
    (F : ℝ → ℝ → ℝ) : pairColeHopfOperator p F = F := by
  funext x y
  cases hk : p.kind <;>
    simp [pairColeHopfOperator, hk, hp, independentPairColeHopf, correlatedPairColeHopf,
      coleHopf_zero_var]

/-- Filtering all zero-variance layers preserves the actual paired
recursion, with no positivity or ordering assumption on its masses. -/
theorem pairColeHopfIterate_map_filter_zero_variance {α : Type*}
    (l : List α) (ps : α → PairColeHopfLevel) (test : α → Bool)
    (hz : ∀ e ∈ l, test e = false → (ps e).variance = 0) (F : ℝ → ℝ → ℝ) :
    pairColeHopfIterate (l.map ps) F = pairColeHopfIterate ((l.filter test).map ps) F := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    have hzt : ∀ a ∈ l, test a = false → (ps a).variance = 0 :=
      fun a ha => hz a (List.mem_cons_of_mem _ ha)
    cases he : test e with
    | false =>
      simp only [List.map_cons, pairColeHopfIterate,
        pairColeHopfOperator_zero_variance_eq _ (hz e List.mem_cons_self he),
        List.filter_cons, he, Bool.false_eq_true, ite_false, ih hzt]
    | true =>
      simp only [List.filter_cons, he, ite_true, List.map_cons, pairColeHopfIterate, ih hzt]

end SpinGlass
