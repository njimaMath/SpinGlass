import SpinGlass.Parisi.Coupled.CoupledCanonicalPath

/-!
# Concrete endpoints of the canonical driven path

The exact driven projection of the physical merge gives the path values
on both sides of every driven piece. The finite split-block walk proves
these identities at root, interior and terminal intervals, without a
strict overlap assumption or an assumed covariance identity.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

noncomputable def ParisiCanonicalPiece.intervalLower {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (_p : Fin (k + 2)) (u : ℝ) : ParisiCanonicalPiece k → ℝ
  | .auxiliary _ => 0
  | .driven i => qExt qs i.val
  | .splitRight => u

noncomputable def ParisiCanonicalPiece.intervalUpper {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 2)) (u : ℝ) : ParisiCanonicalPiece k → ℝ
  | .auxiliary _ => 0
  | .driven i => if i = p then u else qExt qs (i.val + 1)
  | .splitRight => qExt qs (p.val + 1)

theorem ParisiCanonicalPiece.profileIncrement_eq_endpoints {k : ℕ}
    (θ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 2)) (u : ℝ)
    (e : ParisiCanonicalPiece k) :
    e.profileIncrement θ qs p u =
      θ (e.intervalUpper qs p u) - θ (e.intervalLower qs p u) := by
  cases e with
  | auxiliary i => simp [profileIncrement, intervalLower, intervalUpper]
  | driven i =>
    by_cases hi : i = p <;> simp [profileIncrement, intervalLower, intervalUpper, hi]
  | splitRight => rfl

def parisiCanonicalDrivenWalk {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (p : Fin (k + 2)) (u : ℝ) : ℝ → List (ParisiCanonicalPiece k) → Prop
  | _, [] => True
  | x, e :: l => e.intervalLower qs p u = x ∧
      parisiCanonicalDrivenWalk qs p u (e.intervalUpper qs p u) l

theorem parisiCanonicalDrivenWalk_block_append_iff {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p i : Fin (k + 2)) (u : ℝ)
    (tail : List (ParisiCanonicalPiece k)) :
    parisiCanonicalDrivenWalk qs p u (qExt qs i.val)
        (parisiCanonicalDrivenBlock p i ++ tail) ↔
      parisiCanonicalDrivenWalk qs p u (qExt qs (i.val + 1)) tail := by
  by_cases hi : i = p <;>
    simp [parisiCanonicalDrivenBlock, hi, parisiCanonicalDrivenWalk,
      ParisiCanonicalPiece.intervalLower, ParisiCanonicalPiece.intervalUpper]

theorem parisiCanonicalDrivenWalk_ofFn {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (p : Fin (k + 2)) (u : ℝ) (a n : ℕ) (ha : a + n ≤ k + 2) :
    parisiCanonicalDrivenWalk qs p u (qExt qs a)
      ((List.ofFn (fun i : Fin n => (⟨a + i.val, by omega⟩ : Fin (k + 2)))).flatMap
        (parisiCanonicalDrivenBlock p)) := by
  induction n generalizing a with
  | zero => simp [parisiCanonicalDrivenWalk]
  | succ n ih =>
    have ha' : (a + 1) + n ≤ k + 2 := by omega
    have hf :
        (fun i : Fin n => (⟨a + i.succ.val, by omega⟩ : Fin (k + 2))) =
        (fun i : Fin n => (⟨(a + 1) + i.val, by omega⟩ : Fin (k + 2))) := by
      funext i
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [List.ofFn_succ]
    simp only [List.flatMap_cons, Fin.val_zero, Nat.add_zero]
    rw [parisiCanonicalDrivenWalk_block_append_iff qs p (⟨a, by omega⟩ : Fin (k + 2)) u, hf]
    exact ih (a + 1) ha'

/-- The actual driven source traverses its split intervals in order,
starting at zero. No endpoint matching is an input to this theorem. -/
theorem parisiCanonicalDrivenPieces_walk {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 2)) (u : ℝ) :
    parisiCanonicalDrivenWalk qs p u 0 (parisiCanonicalDrivenPieces p) := by
  have hw := parisiCanonicalDrivenWalk_ofFn qs p u 0 (k + 2) (by omega)
  have hf : (fun i : Fin (k + 2) =>
      (⟨0 + i.val, by omega⟩ : Fin (k + 2))) = id := by
    funext i
    apply Fin.ext
    simp
  simpa only [qExt_zero, hf, parisiCanonicalDrivenPieces, parisiCanonicalIndices] using hw

theorem parisiCanonicalDrivenWalk_prefix_sum {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 2)) (u : ℝ)
    (pre post : List (ParisiCanonicalPiece k)) (e : ParisiCanonicalPiece k) {x : ℝ}
    (hw : parisiCanonicalDrivenWalk qs p u x (pre ++ e :: post)) :
    (pre.map (ParisiCanonicalPiece.profileIncrement id qs p u)).sum =
      e.intervalLower qs p u - x := by
  induction pre generalizing x with
  | nil =>
    have hx : e.intervalLower qs p u = x := hw.1
    simp only [List.map_nil, List.sum_nil, hx, sub_self]
  | cons a pre ih =>
    have hx : a.intervalLower qs p u = x := hw.1
    have ht := hw.2
    rw [List.map_cons, List.sum_cons,
      ParisiCanonicalPiece.profileIncrement_eq_endpoints, ih ht]
    simp only [id_eq]
    rw [hx]
    ring

theorem sum_parisiCanonicalProfileIncrement_filter_driven {k : ℕ}
    (θ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 2)) (u : ℝ)
    (l : List (ParisiCanonicalPiece k)) :
    ((l.filter ParisiCanonicalPiece.isDriven).map
      (ParisiCanonicalPiece.profileIncrement θ qs p u)).sum =
        (l.map (ParisiCanonicalPiece.profileIncrement θ qs p u)).sum := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    cases e with
    | auxiliary i =>
      simp only [List.filter_cons, ParisiCanonicalPiece.isDriven, Bool.false_eq_true,
        ite_false, List.map_cons, List.sum_cons, ParisiCanonicalPiece.profileIncrement,
        zero_add, ih]
    | driven i =>
      simp only [List.filter_cons, ParisiCanonicalPiece.isDriven, ite_true,
        List.map_cons, List.sum_cons, ih]
    | splitRight =>
      simp only [List.filter_cons, ParisiCanonicalPiece.isDriven, ite_true,
        List.map_cons, List.sum_cons, ih]

/-- The prefix before each driven piece has exactly that piece's
lower endpoint, obtained from the concrete source-list walk. -/
theorem sum_parisiCanonicalMerged_prefix_eq_lower {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ)
    (pre post : List (ParisiCanonicalPiece k)) (e : ParisiCanonicalPiece k)
    (he : e.isDriven = true) (hl : parisiCanonicalMergedPieces ms r p = pre ++ e :: post) :
    (pre.map (ParisiCanonicalPiece.profileIncrement id qs p u)).sum =
      e.intervalLower qs p u := by
  have hw : parisiCanonicalDrivenWalk qs p u 0
      ((parisiCanonicalMergedPieces ms r p).filter ParisiCanonicalPiece.isDriven) := by
    rw [parisiCanonicalMergedPieces_filter_driven ms hm r p]
    exact parisiCanonicalDrivenPieces_walk qs p u
  have hw' : parisiCanonicalDrivenWalk qs p u 0
      (pre.filter ParisiCanonicalPiece.isDriven ++
        e :: post.filter ParisiCanonicalPiece.isDriven) := by
    simpa only [hl, List.filter_append, List.filter_cons, he, ite_true] using hw
  have hs := parisiCanonicalDrivenWalk_prefix_sum qs p u
    (pre.filter ParisiCanonicalPiece.isDriven) (post.filter ParisiCanonicalPiece.isDriven) e hw'
  rw [sum_parisiCanonicalProfileIncrement_filter_driven, sub_zero] at hs
  exact hs

/-- Evaluating the indexed physical path on both sides of an actual
driven piece gives its exact split interval endpoints. -/
theorem parisiCanonicalOverlapPath_driven_endpoints {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ) (n : Fin (2 * k + 5))
    (he : ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).isDriven = true) :
    parisiCanonicalOverlapPath ms qs r p u n.val =
      ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).intervalLower qs p u ∧
    parisiCanonicalOverlapPath ms qs r p u (n.val + 1) =
      ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).intervalUpper qs p u := by
  let l := parisiCanonicalMergedPieces ms r p
  have hn : n.val < l.length := by simpa [l] using n.isLt
  have hl : l = l.take n.val ++ l[n.val] :: l.drop (n.val + 1) := by
    rw [List.getElem_cons_drop hn]
    exact (List.take_append_drop n.val l).symm
  have hs := sum_parisiCanonicalMerged_prefix_eq_lower ms qs hm r p u
    (l.take n.val) (l.drop (n.val + 1)) l[n.val] he hl
  change parisiCanonicalOverlapPath ms qs r p u n.val = _ at hs
  refine ⟨hs, ?_⟩
  rw [parisiCanonicalOverlapPath_step, hs,
    ParisiCanonicalPiece.profileIncrement_eq_endpoints]
  simp only [id_eq]
  ring

theorem parisiCanonicalOverlapPath_driven_piece_endpoints {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p i : Fin (k + 2)) (u : ℝ) (n : Fin (2 * k + 5))
    (he : (parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt) = .driven i) :
    parisiCanonicalOverlapPath ms qs r p u n.val = qExt qs i.val ∧
      parisiCanonicalOverlapPath ms qs r p u (n.val + 1) =
        if i = p then u else qExt qs (i.val + 1) := by
  have hd : ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).isDriven = true := by
    rw [he]
    rfl
  simpa only [he, ParisiCanonicalPiece.intervalLower, ParisiCanonicalPiece.intervalUpper] using
    parisiCanonicalOverlapPath_driven_endpoints ms qs hm r p u n hd

theorem parisiCanonicalOverlapPath_splitRight_endpoints {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ) (n : Fin (2 * k + 5))
    (he : (parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt) = .splitRight) :
    parisiCanonicalOverlapPath ms qs r p u n.val = u ∧
      parisiCanonicalOverlapPath ms qs r p u (n.val + 1) = qExt qs (p.val + 1) := by
  have hd : ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).isDriven = true := by
    rw [he]
    rfl
  simpa only [he, ParisiCanonicalPiece.intervalLower, ParisiCanonicalPiece.intervalUpper] using
    parisiCanonicalOverlapPath_driven_endpoints ms qs hm r p u n hd

/-- Arbitrary profile increments along the actual merged path are
the labelled increments, providing the diagonal covariance and correction bridge. -/
theorem parisiCanonicalOverlapPath_profile_step {k : ℕ}
    (θ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ) (n : Fin (2 * k + 5)) :
    θ (parisiCanonicalOverlapPath ms qs r p u (n.val + 1)) -
        θ (parisiCanonicalOverlapPath ms qs r p u n.val) =
      ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).profileIncrement θ qs p u := by
  cases he : (parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt) with
  | auxiliary i =>
    rw [parisiCanonicalOverlapPath_auxiliary_step ms qs r p i u n he]
    simp only [sub_self, he, ParisiCanonicalPiece.profileIncrement]
  | driven i =>
    have hends := parisiCanonicalOverlapPath_driven_piece_endpoints ms qs hm r p i u n he
    rw [hends.1, hends.2]
    by_cases hi : i = p <;> simp [ParisiCanonicalPiece.profileIncrement, hi]
  | splitRight =>
    have hends := parisiCanonicalOverlapPath_splitRight_endpoints ms qs hm r p u n he
    rw [hends.1, hends.2]
    rfl

end SpinGlass
