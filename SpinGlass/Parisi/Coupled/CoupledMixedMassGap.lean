import SpinGlass.Parisi.Coupled.CoupledPairGap

/-!
# Strict paired comparison from mixed effective masses

An independent nonzero mark with smaller effective mass than a positive
nonzero correlated mark makes the sorted scalar bound strict. Equality
would force active scalar order, placing the independent mark earlier;
the actual paired Gaussian gap then contradicts equality.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

theorem exists_tail_of_active_scalar_order (l : List PairColeHopfLevel) (q p : PairColeHopfLevel)
    (hq : q ∈ l) (hp : p ∈ l) (hqv : q.variance ≠ 0) (hpv : p.variance ≠ 0)
    (hqp : q.scalar.1 < p.scalar.1)
    (hactive : List.Pairwise parisiActiveLevelMassOrder (pairColeHopfScalarLevels l)) :
    ∃ pre tail, l = pre ++ q :: tail ∧ p ∈ tail := by
  have hact : List.Pairwise (fun a b : PairColeHopfLevel => parisiActiveLevelMassOrder a.scalar b.scalar) l :=
    List.pairwise_map.1 hactive
  obtain ⟨pre, tail, hl⟩ := List.mem_iff_append.1 hq
  subst l
  refine ⟨pre, tail, rfl, ?_⟩
  rcases List.mem_append.1 hp with hp | hp
  · have hrel := (List.pairwise_append.1 hact).2.2 p hp q (List.mem_cons_self)
    change p.variance = 0 ∨ q.variance = 0 ∨ p.scalar.1 ≤ q.scalar.1 at hrel
    rcases hrel with hpzero | hqzero | hle
    · exact (hpv hpzero).elim
    · exact (hqv hqzero).elim
    · exact (not_le_of_gt hqp hle).elim
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact (lt_irrefl _ hqp).elim
    · exact hp

/-- The strict version of the paired/sorted comparison from actual
independent and correlated mark witnesses. Active order and a pressure
gap are conclusions of the proof, not assumptions. -/
theorem randomFieldPairColeHopfListValue_lt_sorted_of_mixed_mass
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (l : List PairColeHopfLevel) (hm : ∀ z ∈ l, 0 ≤ z.mass)
    (hscalar : ∀ z ∈ pairColeHopfScalarLevels l, z.1 ∈ Icc (0 : ℝ) 1)
    (q p : PairColeHopfLevel) (hq : q ∈ l) (hp : p ∈ l)
    (hqkind : q.kind = .independent) (hqv : q.variance ≠ 0)
    (hpkind : p.kind ≠ .independent) (hppos : 0 < p.mass) (hpv : p.variance ≠ 0)
    (hqp : q.scalar.1 < p.scalar.1) :
    randomFieldPairColeHopfListValue μh l <
      2 * randomFieldColeHopfListValue μh (List.insertionSort parisiLevelMassOrder (pairColeHopfScalarLevels l)) := by
  apply lt_of_le_of_ne (randomFieldPairColeHopfListValue_le_sorted_scalar hμ l hm)
  intro he
  have hactive := parisiActiveLevelMassOrder_of_randomFieldPair_sort_eq hμ l hm hscalar he
  obtain ⟨pre, tail, hl, hptail⟩ := exists_tail_of_active_scalar_order l q p hq hp hqv hpv hqp hactive
  subst l
  have hpre : ∀ z ∈ pre, 0 ≤ z.mass := fun z hz => hm z (List.mem_append_left _ hz)
  have htail : ∀ z ∈ tail, 0 ≤ z.mass := fun z hz =>
    hm z (List.mem_append_right _ (List.mem_cons_of_mem _ hz))
  have hstail : ∀ z ∈ pairColeHopfScalarLevels tail, z.1 ∈ Icc (0 : ℝ) 1 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hz
    exact hscalar a.scalar (List.mem_map.2 ⟨a, List.mem_append_right _ (List.mem_cons_of_mem _ ha), rfl⟩)
  have hs := randomFieldPairColeHopfListValue_lt_scalar_of_independent_before_correlated hμ pre tail q
    hpre (hm q hq) hqkind hqv htail hstail ⟨p, hptail, hpkind, hppos, hpv⟩
  have hsort := randomFieldColeHopfListValue_le_insertionSort hμ _
    (pairColeHopfScalarLevels_mass_nonneg (pre ++ q :: tail) hm)
  rw [he] at hs
  linarith

end SpinGlass
