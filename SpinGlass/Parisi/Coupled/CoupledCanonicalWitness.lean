import SpinGlass.Parisi.Coupled.CoupledCanonicalOrder

/-!
# Concrete mass and variance witnesses in the canonical merge

Strict original parameters give strict finite extended chains. The
actual Gaussian variances, including root and terminal intervals, are
positive from the profile derivative. Split variances use admissible
strict overlap inequalities rather than positivity assumed at zero.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

theorem ParisiMAdmissible.strictMono_mExt_fin {k : ℕ} {ms : Fin k → ℝ} (hm : ParisiMAdmissible ms) :
    StrictMono (fun i : Fin (k + 2) => mExt ms i.val) := by
  intro i j hij
  have hi : i.val < k + 1 := by omega
  have hs := sub_pos.1 (hm.mExt_gap_pos (⟨i.val, hi⟩ : Fin (k + 1)))
  change mExt ms i.val < mExt ms (i.val + 1) at hs
  exact hs.trans_le (hm.monotone_mExt (by change i.val + 1 ≤ j.val; omega))

theorem ParisiQAdmissible.monotone_qExt {k : ℕ} {qs : Fin (k + 1) → ℝ} (hq : ParisiQAdmissible qs) :
    Monotone (qExt qs) := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n ≤ k + 1
  · exact qExt_le_succ hq.monotone hq.2.1 hq.2.2 hn
  · rw [qExt_of_le qs (by omega : k + 2 ≤ n), qExt_of_le qs (by omega : k + 2 ≤ n + 1)]

theorem ParisiQAdmissible.strictMono_qExt_fin {k : ℕ} {qs : Fin (k + 1) → ℝ} (hq : ParisiQAdmissible qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) :
    StrictMono (fun i : Fin (k + 3) => qExt qs i.val) := by
  intro i j hij
  have hs := qExt_strict_succ hq.1 hq0 hq1 (r := i.val) (by omega)
  exact hs.trans_le (hq.monotone_qExt (by omega))

theorem parisiAllVars_pos_of_strict_endpoints {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) (i : Fin (k + 2)) :
    0 < parisiAllVars ξ qs i := by
  apply Real.toNNReal_pos.2
  apply sub_pos.2
  exact hξ.strictMonoOn_deriv (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 i.val)
    (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 (i.val + 1))
    (qExt_strict_succ hq.1 hq0 hq1 (by omega))

theorem parisiCanonicalAuxiliaryVariance_pos {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) (p i : Fin (k + 2))
    {t : ℝ} (ht : t < 1) (u : ℝ) :
    0 < (ParisiCanonicalPiece.auxiliary i).variance ξ qs p t u :=
  mul_pos (Real.toNNReal_pos.2 (sub_pos.2 ht)) (parisiAllVars_pos_of_strict_endpoints hξ qs hq hq0 hq1 i)

theorem parisiCanonicalDrivenVariance_pos {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) (p i : Fin (k + 2)) (hi : i ≠ p)
    {t : ℝ} (ht : 0 < t) (u : ℝ) :
    0 < (ParisiCanonicalPiece.driven i).variance ξ qs p t u := by
  simp only [ParisiCanonicalPiece.variance, hi, ite_false]
  exact mul_pos (Real.toNNReal_pos.2 ht) (parisiAllVars_pos_of_strict_endpoints hξ qs hq hq0 hq1 i)

theorem parisiCanonicalSplitLeftVariance_pos {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) (p : Fin (k + 2))
    {t u : ℝ} (ht : 0 < t) (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)))
    (hstrict : qExt qs p.val < u) :
    0 < (ParisiCanonicalPiece.driven p).variance ξ qs p t u := by
  have hlo := qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 p.val
  have hhi := qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 (p.val + 1)
  have humem : u ∈ Icc (0 : ℝ) 1 := ⟨hlo.1.trans hu.1, hu.2.trans hhi.2⟩
  have hd := hξ.strictMonoOn_deriv hlo humem hstrict
  simp only [ParisiCanonicalPiece.variance, ite_true]
  exact mul_pos (Real.toNNReal_pos.2 ht) (Real.toNNReal_pos.2 (sub_pos.2 hd))

theorem parisiCanonicalSplitRightVariance_pos {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) (p : Fin (k + 2))
    {t u : ℝ} (ht : 0 < t) (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)))
    (hstrict : u < qExt qs (p.val + 1)) :
    0 < (ParisiCanonicalPiece.splitRight : ParisiCanonicalPiece k).variance ξ qs p t u := by
  have hlo := qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 p.val
  have hhi := qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 (p.val + 1)
  have humem : u ∈ Icc (0 : ℝ) 1 := ⟨hlo.1.trans hu.1, hu.2.trans hhi.2⟩
  exact mul_pos (Real.toNNReal_pos.2 ht)
    (Real.toNNReal_pos.2 (sub_pos.2 (hξ.strictMonoOn_deriv humem hhi hstrict)))

theorem parisiCanonical_toPair_mem {k : ℕ} (ξ : ℝ → ℝ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2))
    (t u : ℝ) (e : ParisiCanonicalPiece k) :
    e.toPairLevel ξ ms qs negative r p t u ∈ parisiCanonicalPairLevels ξ ms qs negative r p t u :=
  List.mem_map.2 ⟨e, parisiCanonicalPiece_mem_merged ms r p e, rfl⟩

/-- Every positive absolute overlap at most one has an admissible
split with strict lower endpoint. This includes the terminal interval. -/
theorem exists_parisiCanonicalSplit_interval {k : ℕ} (qs : Fin (k + 1) → ℝ)
    {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) :
    ∃ p : Fin (k + 2), u ∈ Ioc (qExt qs p.val) (qExt qs (p.val + 1)) := by
  have hex : ∃ n : ℕ, n ≤ k + 1 ∧ u ≤ qExt qs (n + 1) := by
    refine ⟨k + 1, le_rfl, ?_⟩
    rw [qExt_of_le qs (by omega : k + 2 ≤ k + 1 + 1)]
    exact hu.2
  let n := Nat.find hex
  have hn : n ≤ k + 1 ∧ u ≤ qExt qs (n + 1) := Nat.find_spec hex
  refine ⟨⟨n, by omega⟩, ?_, hn.2⟩
  by_cases hn0 : n = 0
  · simpa only [hn0, qExt_zero] using hu.1
  · have hprev : ¬(n - 1 ≤ k + 1 ∧ u ≤ qExt qs (n - 1 + 1)) :=
      Nat.find_min hex (by dsimp only [n]; omega)
    by_contra hbad
    apply hprev
    refine ⟨by omega, ?_⟩
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
    exact le_of_not_gt hbad

end SpinGlass
