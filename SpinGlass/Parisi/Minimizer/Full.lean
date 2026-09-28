import SpinGlass.Parisi.Minimizer.StrictMass

/-!
# Full

Existence of strict near-optimal MIN parameters.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

set_option maxHeartbeats 1000000

/-- Talagrand's MIN parameters: a near-global optimum which is an exact
minimum over all closed mass and overlap competitors at its level count. -/
theorem exists_randomFieldParisiMIN
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms ∧ ParisiQAdmissible qs ∧
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε ∧
      IsRandomFieldParisiQMinimizer μh ξ ms qs ∧
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) := by
  obtain ⟨k, p, hp, hnear, hmin⟩ :=
    exists_nearOptimal_closedRandomFieldParisiMinimum hμ hξ hε
  obtain ⟨l, ms, qs, _, hm, hq, heq, hmin'⟩ :=
    exists_strictM_closedRandomFieldParisiMinimum μh hξ p.1 p.2 hp.1 hp.2 hmin
  obtain ⟨j, ms', qs', _, hm', hq', heq', hmin''⟩ :=
    exists_strictQ_closedRandomFieldParisiMinimum_of_strictM
      μh ξ ms qs hm hq hmin'
  refine ⟨j, ms', qs', hm', hq', ?_,
    isRandomFieldParisiQMinimizer_of_closedMinimum μh ξ ms' qs' hm' hq' hmin'',
    hmin''⟩
  rw [← closedRandomFieldParisiFunctional_eq μh ξ ms' qs' hm']
  exact (heq'.trans heq).trans_lt hnear

end SpinGlass
