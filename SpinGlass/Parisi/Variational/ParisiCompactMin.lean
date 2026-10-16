import SpinGlass.Parisi.Variational.ParisiMin
import SpinGlass.Parisi.Variational.ParisiParameterContinuity
import SpinGlass.Parisi.Variational.ParisiLevelReduction
import SpinGlass.Parisi.Minimizer.QVariation.RandomField

/-!
# Compact overlap minimization of near-optimal parameter lists

These are intermediate results toward Lemma 14.5.5. They minimize all overlap
coordinates together, while retaining the selected mass list. Full MIN requires
minimization of the masses as well, followed by redundant-level removal.
-/

open MeasureTheory Set

namespace SpinGlass

/-- Infimum selection followed by compact overlap minimization gives a
near-optimal list that minimizes over the entire closed overlap domain. -/
theorem exists_nearOptimal_randomFieldParisiQMinimum
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms ∧ qs ∈ parisiOverlapDomain k ∧
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε ∧
      IsMinOn (fun qs => randomFieldParisiFunctional μh ξ ms qs) (parisiOverlapDomain k) qs := by
  obtain ⟨k, ms, qs₀, hsm, hpos, hlt, hmono, hq0, hq1, hnear⟩ :=
    exists_randomFieldParisiFunctional_lt_inf_add_of_talagrand μh hξ hε
  have hm : ParisiMAdmissible ms := ⟨hsm, hpos, hlt⟩
  obtain ⟨qs, hqs, hmin⟩ := exists_randomFieldParisiQMinimum_of_fixed_masses ms hm hμ hξ
  refine ⟨k, ms, qs, hm, hqs, ?_, hmin⟩
  exact (hmin (mem_parisiOverlapDomain_iff.2 ⟨hmono, hq0, hq1⟩)).trans_lt hnear

/-- Repeated-overlap deletion terminates because every deletion lowers the
number of masses. The value and closed-domain minimality are preserved. -/
theorem exists_strictQMinimum_of_closedQMinimum
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : qs ∈ parisiOverlapDomain k)
    (hmin : IsMinOn (fun qs => randomFieldParisiFunctional μh ξ ms qs)
      (parisiOverlapDomain k) qs) :
    ∃ (l : ℕ) (ms' : Fin l → ℝ) (qs' : Fin (l + 1) → ℝ),
      l ≤ k ∧ ParisiMAdmissible ms' ∧ ParisiQAdmissible qs' ∧
      randomFieldParisiFunctional μh ξ ms' qs' = randomFieldParisiFunctional μh ξ ms qs ∧
      IsMinOn (fun qs => randomFieldParisiFunctional μh ξ ms' qs) (parisiOverlapDomain l) qs' := by
  induction k with
  | zero =>
    have hs : StrictMono qs := Fin.strictMono_iff_lt_succ.2 (fun i => i.elim0)
    have hb := mem_parisiOverlapDomain_iff.1 hq
    exact ⟨0, ms, qs, le_refl _, hm, ⟨hs, hb.2.1, hb.2.2⟩, rfl, hmin⟩
  | succ k ih =>
    by_cases hs : StrictMono qs
    · have hb := mem_parisiOverlapDomain_iff.1 hq
      exact ⟨k + 1, ms, qs, le_refl _, hm, ⟨hs, hb.2.1, hb.2.2⟩, rfl, hmin⟩
    · have hn : ¬ ∀ p : Fin (k + 1), qs p.castSucc < qs p.succ :=
        fun hp => hs (Fin.strictMono_iff_lt_succ.2 hp)
      obtain ⟨p, hp⟩ := not_forall.1 hn
      have he : qs p.castSucc = qs p.succ :=
        le_antisymm (hq.2 p.castSucc_le_succ) (le_of_not_gt hp)
      obtain ⟨l, ms', qs', hl, hm', hq', hvalue, hmin'⟩ :=
        ih (eraseParisiMass ms p) (eraseParisiOverlap qs p)
          (hm.eraseParisiMass p) (eraseParisiOverlap_mem_domain hq p)
          (isMinOn_randomFieldParisiFunctional_erase_adjacent_eq μh ms qs hm p he hmin)
      exact ⟨l, ms', qs', hl.trans (Nat.le_succ k), hm', hq',
        hvalue.trans (randomFieldParisiFunctional_erase_adjacent_eq μh ms qs hm p he), hmin'⟩

/-- A near-optimal list with strict masses and overlaps can be chosen to
minimize over all overlap competitors. This supplies the existing concrete
q-stationarity API; full MIN also requires mass minimality. -/
theorem exists_nearOptimal_randomFieldParisiQMinimizer
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms ∧ IsRandomFieldParisiQMinimizer μh ξ ms qs ∧
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε := by
  obtain ⟨k, ms, qs, hm, hq, hnear, hmin⟩ :=
    exists_nearOptimal_randomFieldParisiQMinimum hμ hξ hε
  obtain ⟨l, ms', qs', _, hm', hq', hvalue, hmin'⟩ :=
    exists_strictQMinimum_of_closedQMinimum μh ξ ms qs hm hq hmin
  refine ⟨l, ms', qs', hm', ⟨hq', ?_⟩, ?_⟩
  · intro qs'' hq''
    exact hmin' (mem_parisiOverlapDomain_iff.2 ⟨hq''.monotone, hq''.2.1, hq''.2.2⟩)
  · exact hvalue.trans_lt hnear

/-- Near-optimal concrete stationary overlap lists exist for a nondegenerate
site law. The moments are those of the actual recursion, not extra hypotheses. -/
theorem exists_nearOptimal_randomFieldParisi_stationary
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : NondegenerateExternalFieldLaw μh) (hξ : TalagrandXiCondition ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms ∧ IsRandomFieldParisiQMinimizer μh ξ ms qs ∧
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε ∧
      (∀ n : ℕ, n ≤ k + 1 → qExt qs n < qExt qs (n + 1)) ∧
      ∀ r, qs r = randomFieldParisiQMoment μh ξ ms qs r := by
  obtain ⟨k, ms, qs, hm, hmin, hnear⟩ :=
    exists_nearOptimal_randomFieldParisiQMinimizer hμ.integrable_id hξ hε
  obtain ⟨hchain, hmom⟩ :=
    randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin ms qs hm hξ hμ hmin
  exact ⟨k, ms, qs, hm, hmin, hnear, hchain, hmom⟩

end SpinGlass
