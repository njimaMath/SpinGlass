import SpinGlass.Parisi.Coupled.CoupledCanonicalMagnitudeGap
import SpinGlass.Parisi.Coupled.CoupledCanonicalRootPrefix

/-!
# Strict signed canonical comparison

The concrete common and antisymmetric root expectations exclude equality
in Proposition 14.8.6 for negative overlaps, except the initial neighboring
interval already covered by Proposition 14.8.3. All Gaussian variances and
positive correlated marks are obtained from the original parameters.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

/-- The signed one-site comparison is strict whenever the original
level is nonroot or the absolute overlap exceeds the first overlap.
The finite-volume pressure transport remains a separate bridge. -/
theorem randomFieldPairColeHopfListValue_parisiCanonical_negative_lt
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {t u : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioc (qExt qs p.val) (qExt qs (p.val + 1)))
    (hfar : 0 < r.val ∨ qs 0 < u) :
    randomFieldPairColeHopfListValue μh
        (parisiCanonicalPairLevels ξ ms qs true r p t u) <
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
      exact (parisiCanonicalSplitLeftVariance_pos hξ qs hq 0 ht.1
        ⟨hu.1.le, hu.2⟩ hu.1).ne'
    · exact (parisiCanonicalDrivenVariance_pos hξ qs hq hq0 hq1 p 0
        (Ne.symm hp) ht.1 u).ne'
  have hcor : ∃ c ∈ l, c.kind ≠ .independent ∧ 0 < c.mass ∧ c.variance ≠ 0 := by
    rcases hfar with hr | huq
    · let c := (ParisiCanonicalPiece.auxiliary r.castSucc).toPairLevel
        ξ ms qs true r p t u
      refine ⟨c, parisiCanonical_toPair_mem ξ ms qs true r p t u _, ?_, ?_, ?_⟩
      · simp [c, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.kind,
          ParisiCanonicalPiece.shared]
      · simpa [c, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.physicalMass,
          ParisiCanonicalPiece.shared, ParisiCanonicalPiece.oldLevel] using
            div_pos (hm.mExt_pos hr) (by norm_num : (0 : ℝ) < 2)
      · exact (parisiCanonicalAuxiliaryVariance_pos hξ qs hq hq0 hq1
          p r.castSucc ht.2 u).ne'
    · have hp : 0 < p.val := by
        by_contra hbad
        have hp0 : p.val = 0 := by omega
        have hupper := hu.2
        rw [hp0, zero_add, qExt_succ_of_lt qs (by omega : 0 < k + 1)] at hupper
        exact (not_lt_of_ge hupper) huq
      let c := (ParisiCanonicalPiece.driven p).toPairLevel ξ ms qs true r p t u
      refine ⟨c, parisiCanonical_toPair_mem ξ ms qs true r p t u _, ?_, ?_, ?_⟩
      · simp [c, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.kind,
          ParisiCanonicalPiece.shared]
      · simpa [c, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.physicalMass,
          ParisiCanonicalPiece.shared, ParisiCanonicalPiece.oldLevel] using
            div_pos (hm.mExt_pos hp) (by norm_num : (0 : ℝ) < 2)
      · exact (parisiCanonicalSplitLeftVariance_pos hξ qs hq p ht.1
          ⟨hu.1.le, hu.2⟩ hu.1).ne'
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
    rw [hl] at hc
    rcases List.mem_cons.1 hc with heq | hc
    · have he : c.mass = 0 := by rw [heq]; exact hqmass
      exact (not_lt_of_ge (he.le) hpos).elim
    · rcases List.mem_cons.1 hc with heq | hc
      · have he : c.mass = 0 := by rw [heq]; exact hdmass
        exact (not_lt_of_ge (he.le) hpos).elim
      · exact ⟨c, hc, hkind, hpos, hv⟩
  have hs := randomFieldPairColeHopfListValue_lt_scalar_of_opposite_before_correlated
    hμ [] tail q d (by simp) (by rw [hqmass]) (by rw [hdmass])
    (Or.inl ⟨hqkind, hdkind⟩) hqv hdv htail hstail hcortail
  have hsort := randomFieldColeHopfListValue_le_insertionSort hμ
    (pairColeHopfScalarLevels l) (pairColeHopfScalarLevels_mass_nonneg l hmass)
  have he := randomFieldColeHopfListValue_parisiCanonical_sorted_eq hξ μh ms qs hm hq
    true r p ⟨ht.1.le, ht.2.le⟩ ⟨hu.1.le, hu.2⟩
  change randomFieldColeHopfListValue μh
    (List.insertionSort parisiLevelMassOrder (pairColeHopfScalarLevels l)) = _ at he
  rw [he] at hsort
  simp only [List.nil_append] at hs
  rw [← hl] at hs
  exact hs.trans_le (mul_le_mul_of_nonneg_left hsort (by norm_num))

/-- The actual signed canonical list has a strict one-site comparison
outside neighboring overlaps, except the initial interval of Proposition
14.8.3. This is the equality exclusion of Proposition 14.8.6; it does
not assume a physical-pressure comparison. -/
theorem exists_randomFieldPairColeHopfListValue_parisiCanonical_outside_gap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1)
    (r : Fin (k + 1)) {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Icc (-1 : ℝ) 1)
    (hfar : u < qExt qs r.val ∨ qExt qs (r.val + 2) < u)
    (hexception : ¬(r.val = 0 ∧ |u| ≤ qs 0)) :
    ∃ p : Fin (k + 2), |u| ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)) ∧
      randomFieldPairColeHopfListValue μh
          (parisiCanonicalPairLevels ξ ms qs (decide (u < 0)) r p t |u|) <
        2 * ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  by_cases hneg : u < 0
  · have habs : |u| ∈ Ioc (0 : ℝ) 1 :=
      ⟨abs_pos.2 (ne_of_lt hneg), abs_le.2 hu⟩
    obtain ⟨p, hp⟩ := exists_parisiCanonicalSplit_interval qs habs
    refine ⟨p, ⟨hp.1.le, hp.2⟩, ?_⟩
    have hf : 0 < r.val ∨ qs 0 < |u| := by
      by_cases hr : 0 < r.val
      · exact Or.inl hr
      · apply Or.inr
        apply lt_of_not_ge
        intro hle
        exact hexception ⟨by omega, hle⟩
    simpa only [hneg, decide_true] using
      randomFieldPairColeHopfListValue_parisiCanonical_negative_lt hμ hξ ms qs
        hm hq hq0 hq1 r p ht hp hf
  · have hnonneg := le_of_not_gt hneg
    have habs : |u| = u := abs_of_nonneg hnonneg
    simpa only [habs, hneg, decide_false] using
      exists_randomFieldPairColeHopfListValue_parisiCanonical_magnitude_gap hμ hξ ms qs
        hm hq hq0 hq1 false r ht ⟨hnonneg, hu.2⟩ hfar

end SpinGlass
