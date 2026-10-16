import SpinGlass.Parisi.Coupled.CoupledCanonicalWitness
import SpinGlass.Parisi.Coupled.CoupledMixedMassGap

/-!
# Strict canonical comparison outside neighboring magnitudes

The independent and correlated witnesses in the positive-overlap
part of Proposition 14.8.6 are actual labelled canonical pieces.
Their scalar masses and nonzero variances are derived from the original
parameters. At a split right endpoint the next driven piece replaces
the zero-variance independent split piece.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

/-- Transfer concrete mixed-mass witnesses to the exact old
canonical scalar comparator. This is a witness reduction used below. -/
theorem randomFieldPairColeHopfListValue_parisiCanonical_lt_of_mixed_mass
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) (q c : PairColeHopfLevel)
    (hqm : q ∈ parisiCanonicalPairLevels ξ ms qs negative r p t u)
    (hcm : c ∈ parisiCanonicalPairLevels ξ ms qs negative r p t u)
    (hqkind : q.kind = .independent) (hqv : q.variance ≠ 0)
    (hckind : c.kind ≠ .independent) (hcpos : 0 < c.mass) (hcv : c.variance ≠ 0)
    (hqc : q.scalar.1 < c.scalar.1) :
    randomFieldPairColeHopfListValue μh (parisiCanonicalPairLevels ξ ms qs negative r p t u) <
      2 * ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  have h := randomFieldPairColeHopfListValue_lt_sorted_of_mixed_mass hμ
    (parisiCanonicalPairLevels ξ ms qs negative r p t u)
    (fun z hz => (parisiCanonicalPairLevels_mass_mem_Icc ξ ms qs hm negative r p t u z hz).1)
    (parisiCanonicalPairLevels_scalar_mass_mem_Icc ξ ms qs hm negative r p t u)
    q c hqm hcm hqkind hqv hckind hcpos hcv hqc
  rw [randomFieldColeHopfListValue_parisiCanonical_sorted_eq hξ μh ms qs hm hq negative r p ht hu] at h
  exact h

/-- The upper outside-neighbor one-site comparison uses the first
independent auxiliary piece and the actual correlated driven split. -/
theorem randomFieldPairColeHopfListValue_parisiCanonical_right_lt
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioc (qExt qs p.val) (qExt qs (p.val + 1))) (hfar : qExt qs (r.val + 2) < u) :
    randomFieldPairColeHopfListValue μh (parisiCanonicalPairLevels ξ ms qs negative r p t u) <
      2 * ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  have hidx : r.succ < p := by
    change r.val + 1 < p.val
    by_contra hbad
    have hqle := hq.monotone_qExt (show p.val + 1 ≤ r.val + 2 by omega)
    exact (not_lt_of_ge (hu.2.trans hqle)) hfar
  let q := (ParisiCanonicalPiece.auxiliary r.succ).toPairLevel ξ ms qs negative r p t u
  let c := (ParisiCanonicalPiece.driven p).toPairLevel ξ ms qs negative r p t u
  apply randomFieldPairColeHopfListValue_parisiCanonical_lt_of_mixed_mass hμ hξ ms qs hm hq negative r p
    ⟨ht.1.le, ht.2.le⟩ ⟨hu.1.le, hu.2⟩ q c
  · exact parisiCanonical_toPair_mem ξ ms qs negative r p t u _
  · exact parisiCanonical_toPair_mem ξ ms qs negative r p t u _
  · simp [q, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.kind, ParisiCanonicalPiece.shared]
  · exact (parisiCanonicalAuxiliaryVariance_pos hξ qs hq hq0 hq1 p r.succ ht.2 u).ne'
  · cases negative <;> simp [c, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.kind,
      ParisiCanonicalPiece.shared]
  · have hmass := hm.mExt_pos (n := p.val) (by omega)
    simpa [c, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.physicalMass,
      ParisiCanonicalPiece.shared, ParisiCanonicalPiece.oldLevel] using div_pos hmass (by norm_num : (0 : ℝ) < 2)
  · exact (parisiCanonicalSplitLeftVariance_pos hξ qs hq p ht.1 ⟨hu.1.le, hu.2⟩ hu.1).ne'
  · dsimp only [q, c]
    rw [ParisiCanonicalPiece.scalar_eq, ParisiCanonicalPiece.scalar_eq]
    exact hm.strictMono_mExt_fin hidx

/-- The lower outside-neighbor one-site comparison, including zero
overlap and the boundary where the independent split variance vanishes. -/
theorem randomFieldPairColeHopfListValue_parisiCanonical_left_lt
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) (hfar : u < qExt qs r.val) :
    randomFieldPairColeHopfListValue μh (parisiCanonicalPairLevels ξ ms qs negative r p t u) <
      2 * ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  have hidx : p < r.castSucc := by
    change p.val < r.val
    by_contra hbad
    have hqle := hq.monotone_qExt (show r.val ≤ p.val by omega)
    exact (not_lt_of_ge (hqle.trans hu.1)) hfar
  have hrpos : 0 < r.val := by change p.val < r.val at hidx; omega
  let c := (ParisiCanonicalPiece.auxiliary r.castSucc).toPairLevel ξ ms qs negative r p t u
  have hcm : c ∈ parisiCanonicalPairLevels ξ ms qs negative r p t u :=
    parisiCanonical_toPair_mem ξ ms qs negative r p t u _
  have hckind : c.kind ≠ .independent := by
    simp [c, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.kind, ParisiCanonicalPiece.shared]
  have hcpos : 0 < c.mass := by
    simpa [c, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.physicalMass,
      ParisiCanonicalPiece.shared, ParisiCanonicalPiece.oldLevel] using
        div_pos (hm.mExt_pos hrpos) (by norm_num : (0 : ℝ) < 2)
  have hcv : c.variance ≠ 0 :=
    (parisiCanonicalAuxiliaryVariance_pos hξ qs hq hq0 hq1 p r.castSucc ht.2 u).ne'
  have hfinish (q : PairColeHopfLevel)
      (hqm : q ∈ parisiCanonicalPairLevels ξ ms qs negative r p t u)
      (hqkind : q.kind = .independent) (hqv : q.variance ≠ 0) (hqc : q.scalar.1 < c.scalar.1) :
      randomFieldPairColeHopfListValue μh (parisiCanonicalPairLevels ξ ms qs negative r p t u) <
        2 * ∫ h, closedParisiX₀ ξ ms qs h ∂μh :=
    randomFieldPairColeHopfListValue_parisiCanonical_lt_of_mixed_mass hμ hξ ms qs hm hq negative r p
      ⟨ht.1.le, ht.2.le⟩ hu q c hqm hcm hqkind hqv hckind hcpos hcv hqc
  rcases lt_or_eq_of_le hu.2 with hstrict | heq
  · let q := (ParisiCanonicalPiece.splitRight : ParisiCanonicalPiece k).toPairLevel ξ ms qs negative r p t u
    apply hfinish q
    · exact parisiCanonical_toPair_mem ξ ms qs negative r p t u _
    · simp [q, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.kind, ParisiCanonicalPiece.shared]
    · exact (parisiCanonicalSplitRightVariance_pos hξ qs hq p ht.1 hu hstrict).ne'
    · dsimp only [q, c]
      rw [ParisiCanonicalPiece.scalar_eq, ParisiCanonicalPiece.scalar_eq]
      exact hm.strictMono_mExt_fin hidx
  · have hnextidx : p.val + 1 < r.val := by
      by_contra hbad
      have hqle := hq.monotone_qExt (show r.val ≤ p.val + 1 by omega)
      rw [← heq] at hqle
      exact (not_lt_of_ge hqle) hfar
    let i : Fin (k + 2) := ⟨p.val + 1, by omega⟩
    have hip : ¬i ≤ p := by change ¬p.val + 1 ≤ p.val; omega
    have hine : i ≠ p := by intro h; exact hip h.le
    let q := (ParisiCanonicalPiece.driven i).toPairLevel ξ ms qs negative r p t u
    apply hfinish q
    · exact parisiCanonical_toPair_mem ξ ms qs negative r p t u _
    · simp [q, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.kind, ParisiCanonicalPiece.shared, hip]
    · exact (parisiCanonicalDrivenVariance_pos hξ qs hq hq0 hq1 p i hine ht.1 u).ne'
    · dsimp only [q, c]
      rw [ParisiCanonicalPiece.scalar_eq, ParisiCanonicalPiece.scalar_eq]
      exact hm.strictMono_mExt_fin (show i < r.castSucc from hnextidx)

/-- A concrete canonical split witnesses strictness at every
nonnegative magnitude outside the neighboring interval. It is not a
finite-volume pressure theorem; the physical transport is a later bridge. -/
theorem exists_randomFieldPairColeHopfListValue_parisiCanonical_magnitude_gap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) (negative : Bool) (r : Fin (k + 1))
    {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hfar : u < qExt qs r.val ∨ qExt qs (r.val + 2) < u) :
    ∃ p : Fin (k + 2), u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)) ∧
      randomFieldPairColeHopfListValue μh (parisiCanonicalPairLevels ξ ms qs negative r p t u) <
        2 * ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  by_cases hu0 : u = 0
  · subst u
    have hroot : (0 : ℝ) ∈ Icc (qExt qs (0 : Fin (k + 2)).val)
        (qExt qs ((0 : Fin (k + 2)).val + 1)) := by
      simp only [Fin.val_zero, qExt_zero, zero_add]
      rw [qExt_succ_of_lt qs (by omega : 0 < k + 1)]
      exact ⟨le_rfl, hq.2.1⟩
    refine ⟨0, hroot, ?_⟩
    rcases hfar with hleft | hright
    · exact randomFieldPairColeHopfListValue_parisiCanonical_left_lt hμ hξ ms qs hm hq hq0 hq1 negative r 0 ht hroot hleft
    · exact (not_lt_of_ge (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 (r.val + 2)).1 hright).elim
  · have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    obtain ⟨p, hp⟩ := exists_parisiCanonicalSplit_interval qs ⟨hupos, hu.2⟩
    refine ⟨p, ⟨hp.1.le, hp.2⟩, ?_⟩
    rcases hfar with hleft | hright
    · exact randomFieldPairColeHopfListValue_parisiCanonical_left_lt hμ hξ ms qs hm hq hq0 hq1 negative r p ht ⟨hp.1.le, hp.2⟩ hleft
    · exact randomFieldPairColeHopfListValue_parisiCanonical_right_lt hμ hξ ms qs hm hq hq0 hq1 negative r p ht hp hright

end SpinGlass
