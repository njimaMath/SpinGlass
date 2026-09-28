import SpinGlass.Parisi.Minimizer.Compact

/-!
# StrictOverlap

Removal of repeated overlap levels.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

set_option maxHeartbeats 1000000

/-- Removing a repeated overlap preserves the extended recursion even when
some mass vanishes. -/
theorem closedParisiX₀_erase_adjacent_eq {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin (k + 1) → ℝ) (qs : Fin (k + 2) → ℝ)
    (p : Fin (k + 1)) (hq : qs p.castSucc = qs p.succ) (h : ℝ) :
    closedParisiX₀ ξ (eraseParisiMass ms p) (eraseParisiOverlap qs p) h =
      closedParisiX₀ ξ ms qs h := by
  unfold closedParisiX₀
  rw [parisiAllMasses_eraseParisiMass, parisiAllVars_eraseParisiOverlap qs p hq]
  have hz : parisiAllVars ξ qs p.castSucc.succ = 0 :=
    parisiVar_eq_zero_of_adjacent_eq qs p hq
  rw [coleHopfIterate_erase_zero_var (k + 2) _ _ p.castSucc.succ hz]

/-- The full extended functional is unchanged by deletion of an empty overlap
interval. This includes the zero-mass boundary of the closed parameter domain. -/
theorem closedRandomFieldParisiFunctional_erase_adjacent_eq
    (μh : Measure ℝ) {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin (k + 1) → ℝ) (qs : Fin (k + 2) → ℝ)
    (p : Fin (k + 1)) (hq : qs p.castSucc = qs p.succ) :
    closedRandomFieldParisiFunctional μh ξ
        (eraseParisiMass ms p) (eraseParisiOverlap qs p) =
      closedRandomFieldParisiFunctional μh ξ ms qs := by
  unfold closedRandomFieldParisiFunctional
  congr 1
  · congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (closedParisiX₀_erase_adjacent_eq ms qs p hq)
  · congr 1
    rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    exact parisiCorrection_erase_adjacent_eq ms qs p hq

/-- Reinsert a mass at the previous mass value. The new coordinate is zero at
the left endpoint, so the closed mass ordering is preserved. -/
def repeatParisiMass {k : ℕ} (ms : Fin k → ℝ) (p : Fin (k + 1)) :
    Fin (k + 1) → ℝ :=
  Fin.insertNth (α := fun _ => ℝ) p (mExt ms p.val) ms

@[simp] theorem erase_repeatParisiMass {k : ℕ}
    (ms : Fin k → ℝ) (p : Fin (k + 1)) :
    eraseParisiMass (repeatParisiMass ms p) p = ms := by
  funext i
  unfold eraseParisiMass repeatParisiMass
  exact Fin.insertNth_apply_succAbove _ _ _ _

theorem repeatParisiMass_mem_domain {k : ℕ} {ms : Fin k → ℝ}
    (hm : ms ∈ parisiMassDomain k) (p : Fin (k + 1)) :
    repeatParisiMass ms p ∈ parisiMassDomain (k + 1) := by
  have hb := mem_parisiMassDomain_iff.1 hm
  have hcoord : ∀ i, repeatParisiMass ms p i ∈ Icc (0 : ℝ) 1 := by
    intro i
    by_cases hi : i = p
    · subst i
      simp only [repeatParisiMass, Fin.insertNth_apply_same]
      exact ⟨mExt_nonneg hb.2.1 _, mExt_le_one hb.2.2 _⟩
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      simpa only [repeatParisiMass, Fin.insertNth_apply_succAbove] using
        (show ms j ∈ Icc (0 : ℝ) 1 from ⟨hb.2.1 j, hb.2.2 j⟩)
  refine mem_parisiMassDomain_iff.2 ⟨?_, (fun i => (hcoord i).1),
    (fun i => (hcoord i).2)⟩
  induction k with
  | zero =>
    intro a b _
    have ha : a = 0 := Fin.eq_zero a
    have hb : b = 0 := Fin.eq_zero b
    rw [ha, hb]
  | succ k =>
    refine Fin.cases ?_ (fun i => ?_) p
    · simp only [repeatParisiMass, Fin.val_zero, mExt_zero]
      exact Fin.insertNth_zero_monotone hb.1 0 (hb.2.1 0)
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [repeatParisiMass, Fin.val_succ, mExt_val_succ]
        change Monotone (Fin.insertNth (α := fun _ => ℝ) (Fin.last (k + 1))
          (ms (Fin.last k)) ms)
        exact Fin.insertNth_last_monotone hb.1 _ (le_refl _)
      · simp only [repeatParisiMass, Fin.val_succ, mExt_val_succ]
        change Monotone (Fin.insertNth (α := fun _ => ℝ) j.castSucc.succ
          (ms j.castSucc) ms)
        exact Fin.insertNth_monotone hb.1 j _ (le_refl _) (hb.1 j.castSucc_le_succ)

theorem eraseParisiMass_mem_domain {k : ℕ} {ms : Fin (k + 1) → ℝ}
    (hm : ms ∈ parisiMassDomain (k + 1)) (p : Fin (k + 1)) :
    eraseParisiMass ms p ∈ parisiMassDomain k := by
  have hb := mem_parisiMassDomain_iff.1 hm
  refine mem_parisiMassDomain_iff.2 ⟨?_, ?_, ?_⟩
  · exact hb.1.comp p.succAboveOrderEmb.monotone
  · exact fun i => hb.2.1 (p.succAbove i)
  · exact fun i => hb.2.2 (p.succAbove i)

/-- A full closed-domain minimum remains a full minimum after an empty
overlap interval is removed. Both mass and overlap competitors are lifted. -/
theorem isMinOn_closedRandomFieldParisiFunctional_erase_adjacent_eq
    (μh : Measure ℝ) {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin (k + 1) → ℝ) (qs : Fin (k + 2) → ℝ)
    (p : Fin (k + 1)) (hq : qs p.castSucc = qs p.succ)
    (hmin : IsMinOn (fun x =>
      closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain (k + 1)) (ms, qs)) :
    IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain k)
      (eraseParisiMass ms p, eraseParisiOverlap qs p) := by
  intro x hx
  change closedRandomFieldParisiFunctional μh ξ
      (eraseParisiMass ms p) (eraseParisiOverlap qs p) ≤
    closedRandomFieldParisiFunctional μh ξ x.1 x.2
  rw [closedRandomFieldParisiFunctional_erase_adjacent_eq μh ms qs p hq]
  have htest := closedRandomFieldParisiFunctional_erase_adjacent_eq μh (ξ := ξ)
    (repeatParisiMass x.1 p) (repeatParisiOverlap x.2 p) p
    (repeatParisiOverlap_adjacent_eq x.2 p)
  simp only [erase_repeatParisiMass, erase_repeatParisiOverlap] at htest
  rw [htest]
  have hcomp : (repeatParisiMass x.1 p, repeatParisiOverlap x.2 p) ∈
      parisiParameterDomain (k + 1) :=
    ⟨repeatParisiMass_mem_domain hx.1 p, repeatParisiOverlap_mem_domain hx.2 p⟩
  exact hmin hcomp

/-- Repeated-overlap deletion preserves full closed-domain minimality. -/
theorem exists_strictQ_closedRandomFieldParisiMinimum
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ms ∈ parisiMassDomain k) (hq : qs ∈ parisiOverlapDomain k)
    (hmin : IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain k) (ms, qs)) :
    ∃ (l : ℕ) (ms' : Fin l → ℝ) (qs' : Fin (l + 1) → ℝ),
      l ≤ k ∧ ms' ∈ parisiMassDomain l ∧ ParisiQAdmissible qs' ∧
      closedRandomFieldParisiFunctional μh ξ ms' qs' =
        closedRandomFieldParisiFunctional μh ξ ms qs ∧
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain l) (ms', qs') := by
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
          (eraseParisiMass_mem_domain hm p) (eraseParisiOverlap_mem_domain hq p)
          (isMinOn_closedRandomFieldParisiFunctional_erase_adjacent_eq
            μh ms qs p he hmin)
      exact ⟨l, ms', qs', hl.trans (Nat.le_succ k), hm', hq',
        hvalue.trans (closedRandomFieldParisiFunctional_erase_adjacent_eq μh ms qs p he),
        hmin'⟩

/-- Near-optimal full minima can be chosen with strict overlap coordinates.
The remaining normalization is removal of repeated or endpoint masses. -/
theorem exists_nearOptimal_strictQ_closedRandomFieldParisiMinimum
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ms ∈ parisiMassDomain k ∧ ParisiQAdmissible qs ∧
      closedRandomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε ∧
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) := by
  obtain ⟨k, p, hp, hnear, hmin⟩ :=
    exists_nearOptimal_closedRandomFieldParisiMinimum hμ hξ hε
  obtain ⟨l, ms, qs, _, hm, hq, hvalue, hmin'⟩ :=
    exists_strictQ_closedRandomFieldParisiMinimum μh ξ p.1 p.2 hp.1 hp.2 hmin
  exact ⟨l, ms, qs, hm, hq, hvalue.trans_lt hnear, hmin'⟩


end SpinGlass
