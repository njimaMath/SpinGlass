import SpinGlass.Parisi.Coupled.CoupledOppositeColeHopf
import SpinGlass.Parisi.Coupled.CoupledParisiCorrection
import SpinGlass.Parisi.Variational.ParisiScalarRegrouping

/-!
# Labelled canonical driven and auxiliary pieces

The lists (14.355) and (14.358) retain their original interval labels.
The driven interval is split at the requested absolute overlap. A root
split retains its extra zero-mass expectation; a terminal split is also
allowed. Sorting uses physical masses, whereas scalar regrouping uses
the original effective masses as in (14.376).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

inductive ParisiCanonicalPiece (k : ℕ)
  | auxiliary (i : Fin (k + 2))
  | driven (i : Fin (k + 2))
  | splitRight
  deriving DecidableEq

def parisiCanonicalIndices (k : ℕ) : List (Fin (k + 2)) := List.ofFn id

def parisiCanonicalDrivenBlock {k : ℕ} (p i : Fin (k + 2)) : List (ParisiCanonicalPiece k) :=
  if i = p then [.driven i, .splitRight] else [.driven i]

def parisiCanonicalAuxiliaryPieces (k : ℕ) : List (ParisiCanonicalPiece k) :=
  (parisiCanonicalIndices k).map .auxiliary

def parisiCanonicalDrivenPieces {k : ℕ} (p : Fin (k + 2)) : List (ParisiCanonicalPiece k) :=
  (parisiCanonicalIndices k).flatMap (parisiCanonicalDrivenBlock p)

def parisiCanonicalGroupedPieces {k : ℕ} (p : Fin (k + 2)) : List (ParisiCanonicalPiece k) :=
  (parisiCanonicalIndices k).flatMap (fun i => .auxiliary i :: parisiCanonicalDrivenBlock p i)

def ParisiCanonicalPiece.oldLevel {k : ℕ} (p : Fin (k + 2)) : ParisiCanonicalPiece k → Fin (k + 2)
  | .auxiliary i => i
  | .driven i => i
  | .splitRight => p

def ParisiCanonicalPiece.shared {k : ℕ} (r : Fin (k + 1)) (p : Fin (k + 2)) :
    ParisiCanonicalPiece k → Bool
  | .auxiliary i => decide (i.val < r.val + 1)
  | .driven i => decide (i ≤ p)
  | .splitRight => false

noncomputable def ParisiCanonicalPiece.physicalMass {k : ℕ} (ms : Fin k → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (e : ParisiCanonicalPiece k) : ℝ :=
  if e.shared r p then mExt ms (e.oldLevel p).val / 2 else mExt ms (e.oldLevel p).val

def ParisiCanonicalPiece.kind {k : ℕ} (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2))
    (e : ParisiCanonicalPiece k) : PairColeHopfKind :=
  if e.shared r p then
    match e with
    | .auxiliary _ => .common
    | _ => if negative then .antisymmetric else .common
  else .independent

noncomputable def ParisiCanonicalPiece.variance {k : ℕ} (ξ : ℝ → ℝ)
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 2)) (t u : ℝ) : ParisiCanonicalPiece k → ℝ≥0
  | .auxiliary i => (1 - t).toNNReal * parisiAllVars ξ qs i
  | .driven i => t.toNNReal *
      (if i = p then (deriv ξ u - deriv ξ (qExt qs i.val)).toNNReal else parisiAllVars ξ qs i)
  | .splitRight => t.toNNReal * (deriv ξ (qExt qs (p.val + 1)) - deriv ξ u).toNNReal

noncomputable def ParisiCanonicalPiece.toPairLevel {k : ℕ} (ξ : ℝ → ℝ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2))
    (t u : ℝ) (e : ParisiCanonicalPiece k) : PairColeHopfLevel :=
  ⟨e.physicalMass ms r p, e.variance ξ qs p t u, e.kind negative r p⟩

def parisiCanonicalPhysicalOrder {k : ℕ} (ms : Fin k → ℝ) (r : Fin (k + 1))
    (p : Fin (k + 2)) (a b : ParisiCanonicalPiece k) : Prop :=
  a.physicalMass ms r p ≤ b.physicalMass ms r p

noncomputable instance {k : ℕ} (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) :
    DecidableRel (parisiCanonicalPhysicalOrder ms r p) := by
  intro a b
  unfold parisiCanonicalPhysicalOrder
  infer_instance

instance {k : ℕ} (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) :
    Std.Total (parisiCanonicalPhysicalOrder ms r p) := ⟨fun _a _b => le_total _ _⟩

instance {k : ℕ} (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) :
    IsTrans (ParisiCanonicalPiece k) (parisiCanonicalPhysicalOrder ms r p) :=
  ⟨fun _ _ _ hab hbc => hab.trans hbc⟩

noncomputable def parisiCanonicalMergedPieces {k : ℕ} (ms : Fin k → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) : List (ParisiCanonicalPiece k) :=
  List.insertionSort (parisiCanonicalPhysicalOrder ms r p)
    (parisiCanonicalAuxiliaryPieces k ++ parisiCanonicalDrivenPieces p)

noncomputable def parisiCanonicalPairLevels {k : ℕ} (ξ : ℝ → ℝ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) :
    List PairColeHopfLevel :=
  (parisiCanonicalMergedPieces ms r p).map (ParisiCanonicalPiece.toPairLevel ξ ms qs negative r p t u)

theorem parisiCanonicalMergedPieces_sorted {k : ℕ} (ms : Fin k → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    List.Pairwise (parisiCanonicalPhysicalOrder ms r p) (parisiCanonicalMergedPieces ms r p) :=
  List.pairwise_insertionSort _ _

theorem parisiCanonicalMergedPieces_perm {k : ℕ} (ms : Fin k → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    (parisiCanonicalMergedPieces ms r p).Perm
      (parisiCanonicalAuxiliaryPieces k ++ parisiCanonicalDrivenPieces p) :=
  List.perm_insertionSort _ _

/-- The scalar mass is the original interval mass, exactly at
both driven split pieces and every shared auxiliary piece. -/
theorem ParisiCanonicalPiece.scalar_eq {k : ℕ} (ξ : ℝ → ℝ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2))
    (t u : ℝ) (e : ParisiCanonicalPiece k) :
    (e.toPairLevel ξ ms qs negative r p t u).scalar =
      (mExt ms (e.oldLevel p).val, e.variance ξ qs p t u) := by
  apply Prod.ext
  · unfold toPairLevel PairColeHopfLevel.scalar physicalMass kind
    by_cases hs : e.shared r p
    · simp only [hs, ite_true]
      cases e <;> cases negative <;> simp <;> ring
    · simp [hs]
  · rfl

theorem ParisiCanonicalPiece.physicalMass_mem_Icc {k : ℕ} (ms : Fin k → ℝ)
    (hm : ParisiMAdmissible ms) (r : Fin (k + 1)) (p : Fin (k + 2)) (e : ParisiCanonicalPiece k) :
    e.physicalMass ms r p ∈ Icc (0 : ℝ) 1 := by
  have h0 := mExt_nonneg (fun i => (hm.2.1 i).le) (e.oldLevel p).val
  have h1 := mExt_le_one (fun i => (hm.2.2 i).le) (e.oldLevel p).val
  unfold physicalMass
  split_ifs <;> constructor <;> linarith

theorem parisiCanonicalPairLevels_mass_mem_Icc {k : ℕ} (ξ : ℝ → ℝ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) :
    ∀ q ∈ parisiCanonicalPairLevels ξ ms qs negative r p t u, q.mass ∈ Icc (0 : ℝ) 1 := by
  intro q hq
  obtain ⟨e, _he, rfl⟩ := List.mem_map.1 hq
  exact e.physicalMass_mem_Icc ms hm r p

theorem parisiCanonicalPairLevels_scalar_mass_mem_Icc {k : ℕ} (ξ : ℝ → ℝ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) :
    ∀ q ∈ pairColeHopfScalarLevels (parisiCanonicalPairLevels ξ ms qs negative r p t u),
      q.1 ∈ Icc (0 : ℝ) 1 := by
  intro q hq
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hq
  obtain ⟨e, _he, rfl⟩ := List.mem_map.1 hz
  rw [e.scalar_eq]
  exact ⟨mExt_nonneg (fun i => (hm.2.1 i).le) _, mExt_le_one (fun i => (hm.2.2 i).le) _⟩

theorem parisiCanonicalSplitVars_add {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) (p : Fin (k + 2))
    {u : ℝ} (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) :
    (deriv ξ u - deriv ξ (qExt qs p.val)).toNNReal +
      (deriv ξ (qExt qs (p.val + 1)) - deriv ξ u).toNNReal = parisiAllVars ξ qs p := by
  have hlo := qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 p.val
  have hhi := qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 (p.val + 1)
  have humem : u ∈ Icc (0 : ℝ) 1 := ⟨hlo.1.trans hu.1, hu.2.trans hhi.2⟩
  have hL : 0 ≤ deriv ξ u - deriv ξ (qExt qs p.val) :=
    sub_nonneg.2 (hξ.strictMonoOn_deriv.monotoneOn hlo humem hu.1)
  have hR : 0 ≤ deriv ξ (qExt qs (p.val + 1)) - deriv ξ u :=
    sub_nonneg.2 (hξ.strictMonoOn_deriv.monotoneOn humem hhi hu.2)
  have hT : 0 ≤ deriv ξ (qExt qs (p.val + 1)) - deriv ξ (qExt qs p.val) := by linarith
  apply NNReal.eq
  simp only [NNReal.coe_add, Real.coe_toNNReal _ hL, Real.coe_toNNReal _ hR,
    parisiAllVars, parisiVar, Real.coe_toNNReal _ hT]
  ring

noncomputable def parisiCanonicalVarianceBlock {k : ℕ} (ξ : ℝ → ℝ)
    (qs : Fin (k + 1) → ℝ) (p i : Fin (k + 2)) (t u : ℝ) : List ℝ≥0 :=
  (ParisiCanonicalPiece.auxiliary i :: parisiCanonicalDrivenBlock p i).map
    (ParisiCanonicalPiece.variance ξ qs p t u)

/-- Equation (14.376) at each actual original interval, including
the split root and terminal intervals and closed time endpoints. -/
theorem parisiCanonicalVarianceBlock_sum {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) (p i : Fin (k + 2))
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) :
    (parisiCanonicalVarianceBlock ξ qs p i t u).sum = parisiAllVars ξ qs i := by
  by_cases hi : i = p
  · subst i
    simp only [parisiCanonicalVarianceBlock, parisiCanonicalDrivenBlock, ite_true,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      ParisiCanonicalPiece.variance]
    rw [← mul_add, parisiCanonicalSplitVars_add hξ qs hq p hu]
    exact (add_comm _ _).trans (nnreal_time_split_sum ht _)
  · simp only [parisiCanonicalVarianceBlock, parisiCanonicalDrivenBlock, hi, ite_false,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      ParisiCanonicalPiece.variance]
    exact (add_comm _ _).trans (nnreal_time_split_sum ht _)

end SpinGlass
