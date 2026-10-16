import SpinGlass.Parisi.Coupled.CoupledCanonicalSignedGap

/-!
# Strict canonical comparison on closed split intervals

At a split lower endpoint the shared left mark has variance zero.
The preceding driven interval supplies a nonzero correlated mark instead.
This proves the one-site strictness for every admissible closed split,
so compact uniformization does not depend on a changing split selection.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- The upper outside-neighbor comparison also holds at a split lower
endpoint. Its preceding driven interval replaces the zero left mark. -/
theorem randomFieldPairColeHopfListValue_parisiCanonical_right_lt_closed
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) (hfar : qExt qs (r.val + 2) < u) :
    randomFieldPairColeHopfListValue μh (parisiCanonicalPairLevels ξ ms qs negative r p t u) <
      2 * ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  rcases lt_or_eq_of_le hu.1 with hstrict | heq
  · exact randomFieldPairColeHopfListValue_parisiCanonical_right_lt hμ hξ ms qs hm hq
      hq0 hq1 negative r p ht ⟨hstrict, hu.2⟩ hfar
  · have hp : r.val + 2 < p.val := by
      by_contra hn
      have hh := hq.monotone_qExt (show p.val ≤ r.val + 2 by omega)
      rw [heq] at hh
      exact not_lt_of_ge hh hfar
    let i : Fin (k + 2) := ⟨p.val - 1, by omega⟩
    have hip : i < p := by change p.val - 1 < p.val; omega
    have hidx : r.succ < i := by change r.val + 1 < p.val - 1; omega
    let q := (ParisiCanonicalPiece.auxiliary r.succ).toPairLevel ξ ms qs negative r p t u
    let c := (ParisiCanonicalPiece.driven i).toPairLevel ξ ms qs negative r p t u
    apply randomFieldPairColeHopfListValue_parisiCanonical_lt_of_mixed_mass hμ hξ ms qs hm hq
      negative r p ⟨ht.1.le, ht.2.le⟩ hu q c
    · exact parisiCanonical_toPair_mem ξ ms qs negative r p t u _
    · exact parisiCanonical_toPair_mem ξ ms qs negative r p t u _
    · simp [q, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.kind,
        ParisiCanonicalPiece.shared]
    · exact (parisiCanonicalAuxiliaryVariance_pos hξ qs hq hq0 hq1 p r.succ ht.2 u).ne'
    · cases negative <;> simp [c, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.kind,
        ParisiCanonicalPiece.shared, hip.le]
    · have hmass := hm.mExt_pos (n := i.val) (by change 0 < p.val - 1; omega)
      simpa [c, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.physicalMass,
        ParisiCanonicalPiece.shared, ParisiCanonicalPiece.oldLevel, hip.le] using
          div_pos hmass (by norm_num : (0 : ℝ) < 2)
    · exact (parisiCanonicalDrivenVariance_pos hξ qs hq hq0 hq1 p i hip.ne ht.1 u).ne'
    · dsimp only [q, c]
      rw [ParisiCanonicalPiece.scalar_eq, ParisiCanonicalPiece.scalar_eq]
      exact hm.strictMono_mExt_fin hidx

/-- The actual opposite root directions give strictness on a closed
split whenever a nonzero positive correlated tail piece is exhibited. -/
theorem randomFieldPairColeHopfListValue_parisiCanonical_negative_lt_of_correlated
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {t u : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)))
    (hu0 : 0 < u)
    (hcor : ∃ c ∈ parisiCanonicalPairLevels ξ ms qs true r p t u,
      c.kind ≠ .independent ∧ 0 < c.mass ∧ c.variance ≠ 0) :
    randomFieldPairColeHopfListValue μh (parisiCanonicalPairLevels ξ ms qs true r p t u) <
      2 * ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  let l := parisiCanonicalPairLevels ξ ms qs true r p t u
  let q := (ParisiCanonicalPiece.auxiliary 0).toPairLevel ξ ms qs true r p t u
  let d := (ParisiCanonicalPiece.driven 0).toPairLevel ξ ms qs true r p t u
  obtain ⟨tail, hl⟩ := parisiCanonicalPairLevels_root_prefix ξ ms qs hm true r p t u
  change l = q :: d :: tail at hl
  have hmass : ∀ z ∈ l, 0 ≤ z.mass := fun z hz =>
    (parisiCanonicalPairLevels_mass_mem_Icc ξ ms qs hm true r p t u z hz).1
  have hscalar : ∀ z ∈ pairColeHopfScalarLevels l, z.1 ∈ Icc (0 : ℝ) 1 :=
    parisiCanonicalPairLevels_scalar_mass_mem_Icc ξ ms qs hm true r p t u
  have hqmass : q.mass = 0 := parisiCanonicalAuxiliaryRoot_mass_zero ms r p
  have hdmass : d.mass = 0 := parisiCanonicalDrivenRoot_mass_zero ms r p
  have hqkind : q.kind = .common := by
    simp [q, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.kind,
      ParisiCanonicalPiece.shared]
  have hdkind : d.kind = .antisymmetric := by
    simp [d, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.kind,
      ParisiCanonicalPiece.shared]
  have hqv : q.variance ≠ 0 :=
    (parisiCanonicalAuxiliaryVariance_pos hξ qs hq hq0 hq1 p 0 ht.2 u).ne'
  have hdv : d.variance ≠ 0 := by
    by_cases hp : p = 0
    · subst p
      exact (parisiCanonicalSplitLeftVariance_pos hξ qs hq 0 ht.1 hu (by simpa using hu0)).ne'
    · exact (parisiCanonicalDrivenVariance_pos hξ qs hq hq0 hq1 p 0
        (Ne.symm hp) ht.1 u).ne'
  have htail : ∀ z ∈ tail, 0 ≤ z.mass := by
    intro z hz
    apply hmass z
    rw [hl]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)
  have hstail : ∀ z ∈ pairColeHopfScalarLevels tail, z.1 ∈ Icc (0 : ℝ) 1 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hz
    apply hscalar a.scalar
    apply List.mem_map.2
    refine ⟨a, ?_, rfl⟩
    rw [hl]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha)
  have hcortail : ∃ c ∈ tail, c.kind ≠ .independent ∧ 0 < c.mass ∧ c.variance ≠ 0 := by
    obtain ⟨c, hc, hkind, hpos, hv⟩ := hcor
    change c ∈ l at hc
    rw [hl] at hc
    rcases List.mem_cons.1 hc with heq | hc
    · have he : c.mass = 0 := by rw [heq]; exact hqmass
      exact (not_lt_of_ge he.le hpos).elim
    · rcases List.mem_cons.1 hc with heq | hc
      · have he : c.mass = 0 := by rw [heq]; exact hdmass
        exact (not_lt_of_ge he.le hpos).elim
      · exact ⟨c, hc, hkind, hpos, hv⟩
  have hs := randomFieldPairColeHopfListValue_lt_scalar_of_opposite_before_correlated
    hμ [] tail q d (by simp) (by rw [hqmass]) (by rw [hdmass])
    (Or.inl ⟨hqkind, hdkind⟩) hqv hdv htail hstail hcortail
  have hsort := randomFieldColeHopfListValue_le_insertionSort hμ
    (pairColeHopfScalarLevels l) (pairColeHopfScalarLevels_mass_nonneg l hmass)
  have he := randomFieldColeHopfListValue_parisiCanonical_sorted_eq hξ μh ms qs hm hq
    true r p ⟨ht.1.le, ht.2.le⟩ hu
  change randomFieldColeHopfListValue μh
    (List.insertionSort parisiLevelMassOrder (pairColeHopfScalarLevels l)) = _ at he
  rw [he] at hsort
  simp only [List.nil_append] at hs
  rw [← hl] at hs
  exact hs.trans_le (mul_le_mul_of_nonneg_left hsort (by norm_num))

/-- The negative-overlap equality exclusion holds at every admissible
closed split. At a zero split-left variance the preceding interval gives
the required positive correlated tail mark. -/
theorem randomFieldPairColeHopfListValue_parisiCanonical_negative_lt_closed
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {t u : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)))
    (hu0 : 0 < u) (hfar : 0 < r.val ∨ qs 0 < u) :
    randomFieldPairColeHopfListValue μh (parisiCanonicalPairLevels ξ ms qs true r p t u) <
      2 * ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  rcases lt_or_eq_of_le hu.1 with hstrict | heq
  · exact randomFieldPairColeHopfListValue_parisiCanonical_negative_lt hμ hξ ms qs hm hq
      hq0 hq1 r p ht ⟨hstrict, hu.2⟩ hfar
  · apply randomFieldPairColeHopfListValue_parisiCanonical_negative_lt_of_correlated hμ hξ
      ms qs hm hq hq0 hq1 r p ht hu hu0
    rcases hfar with hr | huq
    · let c := (ParisiCanonicalPiece.auxiliary r.castSucc).toPairLevel ξ ms qs true r p t u
      refine ⟨c, parisiCanonical_toPair_mem ξ ms qs true r p t u _, ?_, ?_, ?_⟩
      · simp [c, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.kind,
          ParisiCanonicalPiece.shared]
      · simpa [c, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.physicalMass,
          ParisiCanonicalPiece.shared, ParisiCanonicalPiece.oldLevel] using
            div_pos (hm.mExt_pos hr) (by norm_num : (0 : ℝ) < 2)
      · exact (parisiCanonicalAuxiliaryVariance_pos hξ qs hq hq0 hq1
          p r.castSucc ht.2 u).ne'
    · have hp : 1 < p.val := by
        by_contra hn
        have hh := hq.monotone_qExt (show p.val ≤ 1 by omega)
        rw [heq, qExt_succ_of_lt qs (by omega : 0 < k + 1)] at hh
        exact not_lt_of_ge hh huq
      let i : Fin (k + 2) := ⟨p.val - 1, by omega⟩
      have hip : i < p := by change p.val - 1 < p.val; omega
      let c := (ParisiCanonicalPiece.driven i).toPairLevel ξ ms qs true r p t u
      refine ⟨c, parisiCanonical_toPair_mem ξ ms qs true r p t u _, ?_, ?_, ?_⟩
      · simp [c, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.kind,
          ParisiCanonicalPiece.shared, hip.le]
      · have hmass := hm.mExt_pos (n := i.val) (by change 0 < p.val - 1; omega)
        simpa [c, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.physicalMass,
          ParisiCanonicalPiece.shared, ParisiCanonicalPiece.oldLevel, hip.le] using
            div_pos hmass (by norm_num : (0 : ℝ) < 2)
      · exact (parisiCanonicalDrivenVariance_pos hξ qs hq hq0 hq1 p i hip.ne ht.1 u).ne'

/-- Equality is excluded on every closed canonical split at an
outside signed overlap. The initial exception is retained explicitly. -/
theorem randomFieldPairColeHopfListValue_parisiCanonical_outside_lt_closed
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {t v : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)))
    (hfar : (if negative then -v else v) < qExt qs r.val ∨
      qExt qs (r.val + 2) < (if negative then -v else v))
    (hexception : ¬(r.val = 0 ∧ v ≤ qs 0)) :
    randomFieldPairColeHopfListValue μh (parisiCanonicalPairLevels ξ ms qs negative r p t v) <
      2 * ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  cases negative with
  | false =>
    rcases hfar with hleft | hright
    · exact randomFieldPairColeHopfListValue_parisiCanonical_left_lt hμ hξ ms qs hm hq
        hq0 hq1 false r p ht hv hleft
    · exact randomFieldPairColeHopfListValue_parisiCanonical_right_lt_closed hμ hξ ms qs hm hq
        hq0 hq1 false r p ht hv hright
  | true =>
    by_cases hv0 : v = 0
    · subst v
      have hleft : (0 : ℝ) < qExt qs r.val := by
        rcases hfar with hleft | hright
        · simpa only [Bool.true_eq, ite_true, neg_zero] using hleft
        · have hnonneg := (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 (r.val + 2)).1
          simp only [ite_true, neg_zero] at hright
          exact (not_lt_of_ge hnonneg hright).elim
      exact randomFieldPairColeHopfListValue_parisiCanonical_left_lt hμ hξ ms qs hm hq
        hq0 hq1 true r p ht hv hleft
    · have hvpos : 0 < v := lt_of_le_of_ne
        ((qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 p.val).1.trans hv.1) (Ne.symm hv0)
      have hrole : 0 < r.val ∨ qs 0 < v := by
        by_cases hr : 0 < r.val
        · exact Or.inl hr
        · apply Or.inr
          exact lt_of_not_ge (fun hle => hexception ⟨by omega, hle⟩)
      exact randomFieldPairColeHopfListValue_parisiCanonical_negative_lt_closed hμ hξ ms qs
        hm hq hq0 hq1 r p ht hv hvpos hrole

end SpinGlass
