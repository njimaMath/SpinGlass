import SpinGlass.Parisi.Coupled.CoupledCanonicalEndpoints

/-!
# Canonical driven covariance increments

The concrete path endpoints discharge the Gaussian covariance increment
identities. Signed shared driven marks use the profile's evenness, whereas
auxiliary marks have zero driven variance and unchanged path coordinates.
No positive lower bound on a variance is required.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- Clamping the actual overlap path at the chosen absolute overlap
retains exactly the shared driven increments. -/
theorem parisiCanonicalOverlapPath_clamped_profile_step {k : ℕ}
    (θ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {u : ℝ}
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) (n : Fin (2 * k + 5)) :
    θ (min u (parisiCanonicalOverlapPath ms qs r p u (n.val + 1))) -
        θ (min u (parisiCanonicalOverlapPath ms qs r p u n.val)) =
      if ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).shared r p then
        ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).profileIncrement θ qs p u
      else 0 := by
  cases he : (parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt) with
  | auxiliary i =>
    rw [parisiCanonicalOverlapPath_auxiliary_step ms qs r p i u n he]
    simp only [sub_self, ParisiCanonicalPiece.profileIncrement, ite_self]
  | driven i =>
    obtain ⟨hlo, hhi⟩ := parisiCanonicalOverlapPath_driven_piece_endpoints ms qs hm r p i u n he
    rw [hlo, hhi]
    by_cases hip : i ≤ p
    · have hl : qExt qs i.val ≤ u := (hq.monotone_qExt hip).trans hu.1
      have hh : (if i = p then u else qExt qs (i.val + 1)) ≤ u := by
        split_ifs with hie
        · exact le_rfl
        · exact (hq.monotone_qExt (show i.val + 1 ≤ p.val by
            have hne : i.val ≠ p.val := fun h => hie (Fin.ext h)
            change i.val ≤ p.val at hip
            omega)).trans hu.1
      rw [min_eq_right hl, min_eq_right hh]
      simp only [ParisiCanonicalPiece.shared, hip, decide_true, ite_true]
      by_cases hie : i = p <;> simp [ParisiCanonicalPiece.profileIncrement, hie]
    · have hpi : p.val + 1 ≤ i.val := by change ¬i.val ≤ p.val at hip; omega
      have hl : u ≤ qExt qs i.val := hu.2.trans (hq.monotone_qExt hpi)
      have hh : u ≤ qExt qs (i.val + 1) := hl.trans (hq.monotone_qExt (by omega))
      have hie : i ≠ p := fun h => hip h.le
      simp only [hie, ite_false, min_eq_left hl, min_eq_left hh,
        ParisiCanonicalPiece.shared, hip, decide_false, Bool.false_eq_true, sub_self]
  | splitRight =>
    obtain ⟨hlo, hhi⟩ := parisiCanonicalOverlapPath_splitRight_endpoints ms qs hm r p u n he
    simp only [hlo, hhi, min_self, min_eq_left hu.2, sub_self,
      ParisiCanonicalPiece.shared, Bool.false_eq_true, ite_false]

noncomputable def ParisiCanonicalPiece.drivenVariance {k : ℕ}
    (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 2)) (t u : ℝ)
    (e : ParisiCanonicalPiece k) : ℝ≥0 :=
  if e.isDriven then e.variance ξ qs p t u else 0

noncomputable def ParisiCanonicalPiece.auxiliaryVariance {k : ℕ}
    (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 2)) (t u : ℝ)
    (e : ParisiCanonicalPiece k) : ℝ≥0 :=
  if e.isDriven then 0 else e.variance ξ qs p t u

theorem ParisiCanonicalPiece.drivenVariance_add_auxiliaryVariance {k : ℕ}
    (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 2)) (t u : ℝ)
    (e : ParisiCanonicalPiece k) :
    e.drivenVariance ξ qs p t u + e.auxiliaryVariance ξ qs p t u = e.variance ξ qs p t u := by
  unfold drivenVariance auxiliaryVariance
  split_ifs <;> simp

theorem ParisiCanonicalPiece.profileDerivativeIncrement_nonneg {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (hq : ParisiQAdmissible qs) (p : Fin (k + 2)) {u : ℝ}
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)))
    (e : ParisiCanonicalPiece k) : 0 ≤ e.profileIncrement (deriv ξ) qs p u := by
  have hlo := qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 p.val
  have hhi := qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 (p.val + 1)
  have humem : u ∈ Icc (0 : ℝ) 1 := ⟨hlo.1.trans hu.1, hu.2.trans hhi.2⟩
  cases e with
  | auxiliary i => exact le_rfl
  | driven i =>
    simp only [profileIncrement]
    split_ifs with hip
    · subst i
      exact sub_nonneg.2 (hξ.strictMonoOn_deriv.monotoneOn hlo humem hu.1)
    · exact sub_nonneg.2 (hξ.strictMonoOn_deriv.monotoneOn
        (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 i.val)
        (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 (i.val + 1))
        (hq.monotone_qExt (by omega)))
  | splitRight =>
    exact sub_nonneg.2 (hξ.strictMonoOn_deriv.monotoneOn humem hhi hu.2)

/-- The actual driven variance is the time-scaled derivative increment,
including clamped zero variances and split endpoints. -/
theorem ParisiCanonicalPiece.coe_drivenVariance {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (hq : ParisiQAdmissible qs) (p : Fin (k + 2)) {t u : ℝ} (ht : 0 ≤ t)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) (e : ParisiCanonicalPiece k) :
    (e.drivenVariance ξ qs p t u : ℝ) = t * e.profileIncrement (deriv ξ) qs p u := by
  have hn := e.profileDerivativeIncrement_nonneg hξ qs hq p hu
  cases e with
  | auxiliary i => simp [drivenVariance, isDriven, profileIncrement]
  | driven i =>
    simp only [drivenVariance, isDriven, ite_true, variance, profileIncrement] at hn ⊢
    split_ifs with hip
    · subst i
      simp only [ite_true] at hn
      simp only [NNReal.coe_mul, Real.coe_toNNReal _ ht, Real.coe_toNNReal _ hn]
    · simp only [hip, ite_false] at hn
      simp only [parisiAllVars, parisiVar, NNReal.coe_mul, Real.coe_toNNReal _ ht,
        Real.coe_toNNReal _ hn]
  | splitRight =>
    simp only [drivenVariance, isDriven, ite_true, variance, profileIncrement] at hn ⊢
    simp only [NNReal.coe_mul, Real.coe_toNNReal _ ht, Real.coe_toNNReal _ hn]

/-- Gaussian columns for each of the three actual paired mark kinds. -/
def ParisiCanonicalPiece.gaussianFactor {k : ℕ} (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (e : ParisiCanonicalPiece k) :
    Fin 2 → Fin 2 → ℝ :=
  match e.kind negative r p with
  | .independent => couplingFactorSgn 1 0 0
  | .common => couplingFactorSgn 1 1 0
  | .antisymmetric => couplingFactorSgn (-1) 1 0

theorem ParisiCanonicalPiece.gram_gaussianFactor {k : ℕ} (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (e : ParisiCanonicalPiece k) (l l' : Fin 2) :
    gram (e.gaussianFactor negative r p) l l' =
      if l = l' then 1 else match e.kind negative r p with
        | .independent => 0 | .common => 1 | .antisymmetric => -1 := by
  unfold gaussianFactor
  cases hk : e.kind negative r p
  · exact gram_couplingFactorSgn_of_le le_rfl l l'
  · exact gram_couplingFactorSgn_of_lt (by norm_num) (by omega) l l'
  · exact gram_couplingFactorSgn_of_lt (by norm_num) (by omega) l l'

/-- The concrete Gaussian driven columns have exactly the increments
of the actual signed matrix path, equation (14.156). -/
theorem parisiCanonicalDrivenVariance_mul_gram {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {t u : ℝ} (ht : 0 ≤ t)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)))
    (n : Fin (2 * k + 5)) (l l' : Fin 2) :
    (((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).drivenVariance
        ξ qs p t u : ℝ) *
      gram (((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).gaussianFactor
        negative r p) l l' =
      deriv (parisiTimeProfile ξ t) (parisiCanonicalCouplingRho ms qs negative r p u l l' (n.val + 1)) -
        deriv (parisiTimeProfile ξ t) (parisiCanonicalCouplingRho ms qs negative r p u l l' n.val) := by
  let e := (parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)
  have hdiag := parisiCanonicalOverlapPath_profile_step (deriv ξ) ms qs hm r p u n
  have hclamp := parisiCanonicalOverlapPath_clamped_profile_step (deriv ξ) ms qs hm hq r p hu n
  change (e.drivenVariance ξ qs p t u : ℝ) *
    gram (e.gaussianFactor negative r p) l l' = _
  rw [ParisiCanonicalPiece.coe_drivenVariance hξ qs hq p ht hu,
    ParisiCanonicalPiece.gram_gaussianFactor, deriv_parisiTimeProfile, deriv_parisiTimeProfile]
  by_cases hll : l = l'
  · simp only [parisiCanonicalCouplingRho, hll, ite_true, mul_one]
    rw [← mul_sub, hdiag]
  · simp only [parisiCanonicalCouplingRho, hll, ite_false]
    cases he : e with
    | auxiliary i =>
      have hn := parisiCanonicalCouplingRho_auxiliary_step ms qs negative r p i u n he l l'
      simp only [parisiCanonicalCouplingRho, hll, ite_false] at hn
      rw [hn]
      simp only [he, ParisiCanonicalPiece.profileIncrement, mul_zero, zero_mul, sub_self]
    | driven i =>
      change deriv ξ (min u (parisiCanonicalOverlapPath ms qs r p u (n.val + 1))) -
        deriv ξ (min u (parisiCanonicalOverlapPath ms qs r p u n.val)) =
          if e.shared r p then e.profileIncrement (deriv ξ) qs p u else 0 at hclamp
      rw [he] at hclamp
      cases negative <;>
        simp only [Bool.false_eq_true, ite_false, ite_true,
          deriv_neg_of_even hξ.even]
      all_goals
        by_cases hs : (ParisiCanonicalPiece.driven i).shared r p = true
        · simp only [ParisiCanonicalPiece.kind, hs, ite_true, Bool.false_eq_true, ite_false]
          simp only [hs, ite_true] at hclamp
          have hh := congrArg (fun x : ℝ => t * x) hclamp
          nlinarith only [hh]
        · have hs' : (ParisiCanonicalPiece.driven i).shared r p = false := Bool.eq_false_iff.2 hs
          simp only [ParisiCanonicalPiece.kind, hs', Bool.false_eq_true, ite_false, mul_zero]
          simp only [hs', Bool.false_eq_true, ite_false] at hclamp
          have hh := congrArg (fun x : ℝ => t * x) hclamp
          nlinarith only [hh]
    | splitRight =>
      change deriv ξ (min u (parisiCanonicalOverlapPath ms qs r p u (n.val + 1))) -
        deriv ξ (min u (parisiCanonicalOverlapPath ms qs r p u n.val)) =
          if e.shared r p then e.profileIncrement (deriv ξ) qs p u else 0 at hclamp
      rw [he] at hclamp
      simp only [ParisiCanonicalPiece.shared, Bool.false_eq_true, ite_false] at hclamp
      cases negative <;>
        simp only [Bool.false_eq_true, ite_false, ite_true,
          deriv_neg_of_even hξ.even, he, ParisiCanonicalPiece.kind,
          ParisiCanonicalPiece.shared, mul_zero]
      all_goals
        have hh := congrArg (fun x : ℝ => t * x) hclamp
        nlinarith only [hh]

end SpinGlass
