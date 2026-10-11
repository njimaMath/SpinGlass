import SpinGlass.Parisi.Minimizer.StrictMass

/-!
# Full

Existence of strict near-optimal MIN parameters.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

set_option maxHeartbeats 1000000

/-- The global infimum bounds every closed-domain competitor, including zero
masses and repeated levels. For the split comparisons in Talagrand, Vol. II,
Section 14.7, the competitor may have a different level count from MIN. -/
theorem randomFieldParisiInf_le_closedRandomFieldParisiFunctional
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ)
    {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ}
    (hp : (ms, qs) ∈ parisiParameterDomain k) :
    randomFieldParisiInf μh ξ ≤ closedRandomFieldParisiFunctional μh ξ ms qs := by
  obtain ⟨p, hp', hmin⟩ :=
    exists_closedRandomFieldParisiMinimum_of_fixed_levels k hμ hξ
  obtain ⟨l, ms', qs', _, hm', hq', heq, _⟩ :=
    exists_strictM_closedRandomFieldParisiMinimum μh hξ p.1 p.2 hp'.1 hp'.2 hmin
  have hb := mem_parisiOverlapDomain_iff.1 hq'
  calc
    randomFieldParisiInf μh ξ ≤ randomFieldParisiFunctional μh ξ ms' qs' :=
      randomFieldParisiInf_le μh ξ (bddBelow_randomFieldParisiSet_of_talagrand μh hξ)
        hm'.1 hm'.2.1 hm'.2.2 hb.1 hb.2.1 hb.2.2
    _ = closedRandomFieldParisiFunctional μh ξ ms' qs' :=
      (closedRandomFieldParisiFunctional_eq μh ξ ms' qs' hm').symm
    _ = closedRandomFieldParisiFunctional μh ξ p.1 p.2 := heq
    _ ≤ closedRandomFieldParisiFunctional μh ξ ms qs := hmin hp

/-- Global near-minimality compares MIN with a closed competitor at any level
count. This is the tolerance inequality used for (14.238)-(14.239). -/
theorem randomFieldParisiFunctional_sub_lt_closed_of_near_inf
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ)
    {k l : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ}
    {ms' : Fin l → ℝ} {qs' : Fin (l + 1) → ℝ} {ε : ℝ}
    (hnear : randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε)
    (hp : (ms', qs') ∈ parisiParameterDomain l) :
    randomFieldParisiFunctional μh ξ ms qs - ε <
      closedRandomFieldParisiFunctional μh ξ ms' qs' := by
  have hbound := randomFieldParisiInf_le_closedRandomFieldParisiFunctional hμ hξ hp
  linarith

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
