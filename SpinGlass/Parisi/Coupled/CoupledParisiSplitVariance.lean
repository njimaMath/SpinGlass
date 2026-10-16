import SpinGlass.Parisi.Coupled.CoupledResponseGain
import SpinGlass.Parisi.Coupled.CoupledGaussianMix

/-!
# The actual driven and auxiliary variances of a Parisi split

The driven marks use the inserted overlap list. The auxiliary marks retain
the original Gaussian intervals, with one zero-variance insertion in the
orientation used in (14.310). Their total variances are the concrete matched
response variances in both orientations, including zero time and endpoints.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- Splitting a nonnegative mark variance between times t and 1−t
retains its original total variance, also at t=0 and t=1. -/
theorem nnreal_time_split_sum {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (v : ℝ≥0) :
    t.toNNReal * v + (1 - t).toNNReal * v = v := by
  have he : t.toNNReal + (1 - t).toNNReal = 1 := by
    apply NNReal.eq
    simp only [NNReal.coe_add, Real.coe_toNNReal _ ht.1,
      Real.coe_toNNReal _ (sub_nonneg.2 ht.2), NNReal.coe_one]
    ring
  rw [← add_mul, he, one_mul]

/-- The outer Gaussian piece in an inner split contains both its
driven left variance and the entire old auxiliary variance. -/
theorem nnreal_time_split_complement {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    t.toNNReal * x.toNNReal + (1 - t).toNNReal * (x + y).toNNReal =
      (x + y - t * y).toNNReal := by
  have htarget : 0 ≤ x + y - t * y := by
    nlinarith [mul_nonneg (sub_nonneg.2 ht.2) hy]
  apply NNReal.eq
  simp only [NNReal.coe_add, NNReal.coe_mul, Real.coe_toNNReal _ ht.1,
    Real.coe_toNNReal _ hx, Real.coe_toNNReal _ (sub_nonneg.2 ht.2),
    Real.coe_toNNReal _ (add_nonneg hx hy), Real.coe_toNNReal _ htarget]
  ring

/-- Driven positive-mass mark variances from the actual inserted
overlap list, with the freely chosen total mark dimension. -/
noncomputable def parisiDrivenSplitVars (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t u : ℝ) :
    Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0 :=
  fun i => t.toNNReal * parisiVar ξ (splitParisiOverlap qs p u) (i.val + 1)

/-- The auxiliary insertion for the inner orientation has variance
zero on the new inner piece and the full old variance on the outer piece. -/
noncomputable def parisiInnerAuxSplitVars (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t : ℝ) :
    Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0 :=
  Fin.append (Fin.snoc (fun i => (1 - t).toNNReal * parisiOuterMassPrefixVars ξ qs p i)
      ((1 - t).toNNReal * parisiVar ξ qs (p.val + 1)))
    (Fin.cons 0 (fun i => (1 - t).toNNReal * parisiQSuffixVars ξ qs p i))

/-- The auxiliary insertion for the mirror orientation has variance
zero on the new outer piece and the full old variance on the inner piece. -/
noncomputable def parisiOuterAuxSplitVars (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t : ℝ) :
    Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0 :=
  Fin.append (Fin.snoc (fun i => (1 - t).toNNReal * parisiOuterMassPrefixVars ξ qs p i) 0)
    (Fin.cons ((1 - t).toNNReal * parisiVar ξ qs (p.val + 1))
      (fun i => (1 - t).toNNReal * parisiQSuffixVars ξ qs p i))

/-- The old interval variance is the difference of its actual endpoint
profile derivatives, with the terminal extended endpoint included. -/
theorem parisiVar_at_split_interval (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) :
    parisiVar ξ qs (p.val + 1) =
      (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p)).toNNReal := by
  unfold parisiVar
  rw [qExt_succ_of_lt qs p.isLt]

/-- Both inserted profile increments are nonnegative on the actual
closed overlap interval. No positivity of ξ'' at zero is needed. -/
theorem parisi_split_profile_increments_nonneg {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (hq : ParisiQAdmissible qs)
    {u : ℝ} (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) :
    0 ≤ deriv ξ u - deriv ξ (qs p) ∧
      0 ≤ deriv ξ (qExt qs (p.val + 2)) - deriv ξ u := by
  have hR := qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 (p.val + 2)
  have humem : u ∈ Icc (0 : ℝ) 1 := ⟨(hq.mem_Icc p).1.trans hu.1, hu.2.trans hR.2⟩
  exact ⟨sub_nonneg.2 (hξ.strictMonoOn_deriv.monotoneOn (hq.mem_Icc p) humem hu.1),
    sub_nonneg.2 (hξ.strictMonoOn_deriv.monotoneOn humem hR hu.2)⟩

/-- Equations (14.316)-(14.319) for the actual inner-oriented arrays.
All unchanged marks retain their old variance, and the adjacent pieces
have exactly a−v and v, with v=t(ξ'(q_R)−ξ'(u)). -/
theorem parisiDrivenSplitVars_add_innerAux_eq {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (hq : ParisiQAdmissible qs)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) :
    (fun i => parisiDrivenSplitVars ξ qs p t u i + parisiInnerAuxSplitVars ξ qs p t i) =
      parisiResponseSplitVars ξ qs p (t * (deriv ξ (qExt qs (p.val + 2)) - deriv ξ u)) := by
  obtain ⟨hL, hR⟩ := parisi_split_profile_increments_nonneg hξ qs p hq hu
  funext i
  unfold parisiDrivenSplitVars parisiInnerAuxSplitVars parisiResponseSplitVars
  refine Fin.addCases (fun q => ?_) (fun q => ?_) i
  · simp only [Fin.append_left, Fin.val_castAdd]
    refine Fin.lastCases ?_ (fun r => ?_) q
    · simp only [Fin.snoc_last, Fin.val_last]
      rw [parisiVar_splitParisiOverlap_left, parisiVar_at_split_interval]
      have ha : deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) =
          (deriv ξ u - deriv ξ (qs p)) + (deriv ξ (qExt qs (p.val + 2)) - deriv ξ u) := by ring
      rw [ha]
      exact nnreal_time_split_complement hL hR ht
    · simp only [Fin.snoc_castSucc, Fin.val_castSucc, parisiOuterMassPrefixVars]
      rw [parisiVar_splitParisiOverlap_before ξ qs p u (by omega)]
      exact nnreal_time_split_sum ht _
  · simp only [Fin.append_right, Fin.val_natAdd]
    refine Fin.cases ?_ (fun r => ?_) q
    · simp only [Fin.cons_zero, Fin.val_zero, add_zero]
      rw [show p.val + 1 + 1 = p.val + 2 by omega,
        parisiVar_splitParisiOverlap_right, Real.toNNReal_mul ht.1]
    · simp only [Fin.cons_succ, Fin.val_succ, parisiQSuffixVars]
      rw [show p.val + 1 + (r.val + 1) + 1 = (p.val + r.val + 2) + 1 by omega,
        parisiVar_splitParisiOverlap_after ξ qs p u (by omega)]
      exact nnreal_time_split_sum ht _

/-- The mirror counterpart of (14.316)-(14.319) for the actual arrays.
The adjacent pieces have w and a−w, with w=t(ξ'(u)−ξ'(q_L)). -/
theorem parisiDrivenSplitVars_add_outerAux_eq {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (hq : ParisiQAdmissible qs)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) :
    (fun i => parisiDrivenSplitVars ξ qs p t u i + parisiOuterAuxSplitVars ξ qs p t i) =
      parisiResponseSplitVars ξ qs p
        (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - t * (deriv ξ u - deriv ξ (qs p))) := by
  obtain ⟨hL, hR⟩ := parisi_split_profile_increments_nonneg hξ qs p hq hu
  funext i
  unfold parisiDrivenSplitVars parisiOuterAuxSplitVars parisiResponseSplitVars
  refine Fin.addCases (fun q => ?_) (fun q => ?_) i
  · simp only [Fin.append_left, Fin.val_castAdd]
    refine Fin.lastCases ?_ (fun r => ?_) q
    · simp only [Fin.snoc_last, Fin.val_last]
      rw [parisiVar_splitParisiOverlap_left, add_zero, sub_sub_cancel, Real.toNNReal_mul ht.1]
    · simp only [Fin.snoc_castSucc, Fin.val_castSucc, parisiOuterMassPrefixVars]
      rw [parisiVar_splitParisiOverlap_before ξ qs p u (by omega)]
      exact nnreal_time_split_sum ht _
  · simp only [Fin.append_right, Fin.val_natAdd]
    refine Fin.cases ?_ (fun r => ?_) q
    · simp only [Fin.cons_zero, Fin.val_zero, add_zero]
      rw [show p.val + 1 + 1 = p.val + 2 by omega,
        parisiVar_splitParisiOverlap_right, parisiVar_at_split_interval]
      have ha : deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) =
          (deriv ξ (qExt qs (p.val + 2)) - deriv ξ u) + (deriv ξ u - deriv ξ (qs p)) := by ring
      rw [ha]
      exact nnreal_time_split_complement hR hL ht
    · simp only [Fin.cons_succ, Fin.val_succ, parisiQSuffixVars]
      rw [show p.val + 1 + (r.val + 1) + 1 = (p.val + r.val + 2) + 1 by omega,
        parisiVar_splitParisiOverlap_after ξ qs p u (by omega)]
      exact nnreal_time_split_sum ht _

/-- The driven root mark uses time t times the original root variance. -/
noncomputable def parisiDrivenRootVar (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (t : ℝ) : ℝ≥0 := t.toNNReal * parisiVar ξ qs 0

/-- The auxiliary root mark uses time 1−t times that same variance. -/
noncomputable def parisiAuxRootVar (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (t : ℝ) : ℝ≥0 := (1 - t).toNNReal * parisiVar ξ qs 0

theorem parisiDrivenRootVar_add_aux_eq (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiDrivenRootVar ξ qs t + parisiAuxRootVar ξ qs t = parisiVar ξ qs 0 :=
  nnreal_time_split_sum ht _

/-- The covariance profile of the time-t driven Hamiltonian. -/
def parisiTimeProfile (ξ : ℝ → ℝ) (t : ℝ) : ℝ → ℝ := fun x => t * ξ x

theorem deriv_parisiTimeProfile (ξ : ℝ → ℝ) (t x : ℝ) :
    deriv (parisiTimeProfile ξ t) x = t * deriv ξ x :=
  deriv_const_mul_field t

/-- Scaling the actual profile scales every clamped variance by t
when t is nonnegative; no global differentiability assumption is needed. -/
theorem parisiVar_timeProfile (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) {t : ℝ} (ht : 0 ≤ t) (r : ℕ) :
    parisiVar (parisiTimeProfile ξ t) qs r = t.toNNReal * parisiVar ξ qs r := by
  unfold parisiVar
  rw [deriv_parisiTimeProfile, deriv_parisiTimeProfile, ← mul_sub, Real.toNNReal_mul ht]

/-- The inserted overlap list belongs to the closed parameter domain,
also when the insertion coincides with either old endpoint. -/
theorem splitParisiOverlap_mem_domain_of_admissible {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (hq : ParisiQAdmissible qs)
    {u : ℝ} (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) :
    splitParisiOverlap qs p u ∈ parisiOverlapDomain (k + 1) := by
  apply splitParisiOverlap_mem_domain
    (mem_parisiOverlapDomain_iff.2 ⟨hq.monotone, hq.2.1, hq.2.2⟩) p
  rw [qExt_succ_of_lt qs p.isLt]
  exact hu

/-- Profile derivative increments are nonnegative throughout every
closed admissible overlap list, including the fixed terminal extension. -/
theorem parisiTimeProfile_deriv_qExt_le_succ {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} {qs : Fin (k + 1) → ℝ} (hq : qs ∈ parisiOverlapDomain k)
    {t : ℝ} (ht : 0 ≤ t) (r : ℕ) :
    deriv (parisiTimeProfile ξ t) (qExt qs r) ≤
      deriv (parisiTimeProfile ξ t) (qExt qs (r + 1)) := by
  obtain ⟨hmono, hzero, hone⟩ := mem_parisiOverlapDomain_iff.1 hq
  have hstep : qExt qs r ≤ qExt qs (r + 1) := by
    by_cases hr : r ≤ k + 1
    · exact qExt_le_succ hmono hzero hone hr
    · rw [qExt_of_le qs (by omega), qExt_of_le qs (by omega)]
  rw [deriv_parisiTimeProfile, deriv_parisiTimeProfile]
  exact mul_le_mul_of_nonneg_left
    (hξ.strictMonoOn_deriv.monotoneOn (qExt_mem_Icc hmono hzero hone r)
      (qExt_mem_Icc hmono hzero hone (r + 1)) hstep) ht

/-- The driven array is exactly the variance array used by the coupled
kernel of the time-scaled profile and actual inserted overlap list. -/
theorem parisiDrivenSplitVars_eq_couplingVar (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) {t : ℝ} (ht : 0 ≤ t) (u : ℝ)
    (i : Fin ((p.val + 1) + ((k - p.val) + 1))) :
    parisiDrivenSplitVars ξ qs p t u i =
      couplingVar (parisiTimeProfile ξ t) (qExt (splitParisiOverlap qs p u)) (i.val + 1) :=
  (parisiVar_timeProfile ξ (splitParisiOverlap qs p u) ht (i.val + 1)).symm

/-- The driven root variance has the same identification. -/
theorem parisiDrivenRootVar_eq_couplingVar (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) {t : ℝ} (ht : 0 ≤ t) (u : ℝ) :
    parisiDrivenRootVar ξ qs t =
      couplingVar (parisiTimeProfile ξ t) (qExt (splitParisiOverlap qs p u)) 0 := by
  change _ = parisiVar (parisiTimeProfile ξ t) (splitParisiOverlap qs p u) 0
  rw [parisiVar_timeProfile ξ _ ht, parisiVar_splitParisiOverlap_before ξ qs p u (by omega)]
  rfl

/-- The driven covariance increments required by the finite-volume
coupled theorem are consequences of the actual split parameters. -/
theorem parisiDrivenSplitVars_mul_gram {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (hq : ParisiQAdmissible qs)
    {t u : ℝ} (ht : 0 ≤ t) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (i : Fin ((p.val + 1) + ((k - p.val) + 1))) (l l' : Fin 2) :
    (parisiDrivenSplitVars ξ qs p t u i : ℝ) *
        gram (couplingFactorSgn 1 (p.val + 2) (i.val + 1)) l l' =
      deriv (parisiTimeProfile ξ t)
          (couplingRhoSgn (qExt (splitParisiOverlap qs p u)) 1 (p.val + 2) l l' (i.val + 2)) -
        deriv (parisiTimeProfile ξ t)
          (couplingRhoSgn (qExt (splitParisiOverlap qs p u)) 1 (p.val + 2) l l' (i.val + 1)) := by
  rw [parisiDrivenSplitVars_eq_couplingVar ξ qs p ht u i]
  have hh := couplingVar_mul_gram (J'' := Fin 2) (τ := p.val + 2)
    (by norm_num : (1 : ℝ) ^ 2 = 1)
    (fun x => by simp only [one_mul])
    (parisiTimeProfile_deriv_qExt_le_succ hξ
      (splitParisiOverlap_mem_domain_of_admissible qs p hq hu) ht (i.val + 1)) l l'
  simpa only [gram_sumL] using hh

/-- The root covariance increments are discharged by the same
concrete construction, including the case of zero driven variance. -/
theorem parisiDrivenRootVar_mul_gram {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (hq : ParisiQAdmissible qs)
    {t u : ℝ} (ht : 0 ≤ t) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) (l l' : Fin 2) :
    (parisiDrivenRootVar ξ qs t : ℝ) * gram (couplingFactorSgn 1 (p.val + 2) 0) l l' =
      deriv (parisiTimeProfile ξ t)
          (couplingRhoSgn (qExt (splitParisiOverlap qs p u)) 1 (p.val + 2) l l' 1) -
        deriv (parisiTimeProfile ξ t)
          (couplingRhoSgn (qExt (splitParisiOverlap qs p u)) 1 (p.val + 2) l l' 0) := by
  rw [parisiDrivenRootVar_eq_couplingVar ξ qs p ht u]
  have hh := couplingVar_mul_gram (J'' := Fin 2) (τ := p.val + 2)
    (by norm_num : (1 : ℝ) ^ 2 = 1)
    (fun x => by simp only [one_mul])
    (parisiTimeProfile_deriv_qExt_le_succ hξ
      (splitParisiOverlap_mem_domain_of_admissible qs p hq hu) ht 0) l l'
  simpa only [gram_sumL] using hh

/-- The two-replica overlap sequence of the actual inserted list,
sharing marks through the outer Gaussian piece and splitting afterward. -/
def parisiSplitCouplingRho {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (p : Fin (k + 1)) (u : ℝ) : Fin 2 → Fin 2 → ℕ → ℝ :=
  couplingRhoSgn (qExt (splitParisiOverlap qs p u)) 1 (p.val + 2)

theorem parisiSplitCouplingRho_zero {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (p : Fin (k + 1)) (u : ℝ) (l l' : Fin 2) : parisiSplitCouplingRho qs p u l l' 0 = 0 :=
  couplingRhoSgn_zero _ (qExt_zero _) 1 _ l l'

/-- Every covariance interpolation parameter lies in the profile's
given derivative domain, even at a repeated inserted overlap. -/
theorem parisiSplitCouplingRho_mem_Icc {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (p : Fin (k + 1)) (hq : ParisiQAdmissible qs) {u : ℝ}
    (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) (l l' : Fin 2) (r : ℕ) :
    parisiSplitCouplingRho qs p u l l' r ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hmono, hzero, hone⟩ := mem_parisiOverlapDomain_iff.1
    (splitParisiOverlap_mem_domain_of_admissible qs p hq hu)
  unfold parisiSplitCouplingRho couplingRhoSgn
  split_ifs
  · exact qExt_mem_Icc hmono hzero hone r
  · simpa only [one_mul] using qExt_mem_Icc hmono hzero hone (min r (p.val + 2))

/-- The terminal covariance parameter is one on the diagonal and the
actual constrained overlap off the diagonal. -/
theorem parisiSplitCouplingRho_top {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (p : Fin (k + 1)) (u : ℝ) (l l' : Fin 2) :
    parisiSplitCouplingRho qs p u l l' (((p.val + 1) + ((k - p.val) + 1)) + 1) =
      if l = l' then 1 else u := by
  have hh := couplingRhoSgn_top (qExt (splitParisiOverlap qs p u)) 1
    (τ := p.val + 2) (κ := (p.val + 1) + ((k - p.val) + 1)) (by omega)
    (qExt_of_le _ (by omega)) l l'
  unfold parisiSplitCouplingRho
  simpa only [one_mul, qExt_splitParisiOverlap_inserted] using hh

/-- The actual split therefore has zero terminal diagonal defect. -/
theorem pairDiagDefect_parisiSplitCouplingRho_top (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (u : ℝ) :
    pairDiagDefect ξ u (fun l l' => parisiSplitCouplingRho qs p u l l'
      (((p.val + 1) + ((k - p.val) + 1)) + 1)) = 0 := by
  have he : (fun l l' => parisiSplitCouplingRho qs p u l l'
      (((p.val + 1) + ((k - p.val) + 1)) + 1)) =
      fun l l' => if l = l' then (1 : ℝ) else u :=
    funext fun l => funext fun l' => parisiSplitCouplingRho_top qs p u l l'
  rw [he, pairDiagDefect_diag]

/-- Evenness of the given profile forces its actual derivative at zero
to vanish; this supplies the coupled kernel hypothesis rather than adding it. -/
theorem TalagrandXiCondition.deriv_zero {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) :
    deriv ξ 0 = 0 := by
  have hh := deriv_neg_of_even hξ.even 0
  simp only [neg_zero] at hh
  linarith

theorem deriv_parisiTimeProfile_zero {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) (t : ℝ) :
    deriv (parisiTimeProfile ξ t) 0 = 0 := by
  rw [deriv_parisiTimeProfile, hξ.deriv_zero, mul_zero]

/-- The profile lies above its tangent at every point of its given
derivative domain, without global differentiability assumptions. -/
theorem TalagrandXiCondition.tangent_line_le {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    ξ q + (x - q) * deriv ξ q ≤ ξ x := by
  rcases lt_trichotomy q x with hqx | rfl | hxq
  · have hs := hξ.convex.deriv_le_slope (mem_univ q) (mem_univ x) hqx
      (hξ.hasDeriv q hq).differentiableAt
    have hm := mul_le_mul_of_nonneg_right hs (sub_pos.2 hqx).le
    have he : slope ξ q x * (x - q) = ξ x - ξ q := by
      rw [mul_comm, ← smul_eq_mul]
      exact sub_smul_slope ξ q x
    rw [he] at hm
    linarith
  · simp
  · have hs := hξ.convex.slope_le_deriv (mem_univ x) (mem_univ q) hxq
      (hξ.hasDeriv q hq).differentiableAt
    have hm := mul_le_mul_of_nonneg_right hs (sub_pos.2 hxq).le
    have he : slope ξ x q * (q - x) = ξ q - ξ x := by
      rw [mul_comm, ← smul_eq_mul]
      exact sub_smul_slope ξ x q
    rw [he] at hm
    nlinarith

/-- The tangent inequality required by the driven coupled theorem is
a consequence of the preserved profile contract at nonnegative times. -/
theorem parisiTimeProfile_tangent_line_le {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {t : ℝ} (ht : 0 ≤ t) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    parisiTimeProfile ξ t q + (x - q) * deriv (parisiTimeProfile ξ t) q ≤
      parisiTimeProfile ξ t x := by
  have hh := mul_le_mul_of_nonneg_left (hξ.tangent_line_le hq x) ht
  rw [deriv_parisiTimeProfile]
  dsimp only [parisiTimeProfile]
  nlinarith

/-- The last split-array coordinate is the original terminal mark. -/
def parisiSplitLastIndex {k : ℕ} (p : Fin (k + 1)) :
    Fin ((p.val + 1) + ((k - p.val) + 1)) := ⟨k + 1, by omega⟩

/-- The terminal matching mass is one and is never halved by the
common-prefix normalization, including a terminal outer insertion. -/
theorem halveBelow_parisiResponseSplitMasses_last {k : ℕ}
    (ms : Fin k → ℝ) (p : Fin (k + 1)) :
    halveBelow (p.val + 1) (parisiResponseSplitMasses ms p) (parisiSplitLastIndex p) = 1 := by
  unfold halveBelow
  have hi : ¬(parisiSplitLastIndex p).val < p.val + 1 := by dsimp only [parisiSplitLastIndex]; omega
  have hj : ¬(parisiSplitLastIndex p).val ≤ p.val := by dsimp only [parisiSplitLastIndex]; omega
  rw [ite_eq_right hi, parisiResponseSplitMasses_eq_mExt, ite_eq_right hj]
  change mExt ms (k + 1) = 1
  exact mExt_eq_one_of_le ms (by omega)

/-- The auxiliary mirror variances after the insertion retain exactly
the old interval coordinates, including the first right piece. -/
theorem parisiOuterAuxSplitVars_natAdd (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t : ℝ) (q : Fin ((k - p.val) + 1)) :
    parisiOuterAuxSplitVars ξ qs p t (Fin.natAdd (p.val + 1) q) =
      (1 - t).toNNReal * parisiVar ξ qs (p.val + q.val + 1) := by
  unfold parisiOuterAuxSplitVars
  rw [Fin.append_right]
  refine Fin.cases ?_ (fun r => ?_) q
  · simp
  · simp only [Fin.cons_succ, Fin.val_succ, parisiQSuffixVars]
    congr 1

/-- The last auxiliary mirror variance is always time 1−t times the
original terminal variance, including the terminal split and k=0. -/
theorem parisiOuterAuxSplitVars_last (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t : ℝ) :
    parisiOuterAuxSplitVars ξ qs p t (parisiSplitLastIndex p) =
      (1 - t).toNNReal * parisiVar ξ qs (k + 1) := by
  have hi : parisiSplitLastIndex p = Fin.natAdd (p.val + 1) (Fin.last (k - p.val)) := by
    apply Fin.ext
    simp only [parisiSplitLastIndex, Fin.val_natAdd, Fin.val_last]
    omega
  rw [hi, parisiOuterAuxSplitVars_natAdd]
  congr 1
  congr 1
  simp only [Fin.val_last]
  omega

/-- For every nonroot inner interval, the last auxiliary variance is
the same original terminal variance scaled by 1−t. -/
theorem parisiInnerAuxSplitVars_last (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin k) (t : ℝ) :
    parisiInnerAuxSplitVars ξ qs p.castSucc t (parisiSplitLastIndex p.castSucc) =
      (1 - t).toNNReal * parisiVar ξ qs (k + 1) := by
  let r : Fin (k - p.val) := ⟨k - p.val - 1, by omega⟩
  have hi : parisiSplitLastIndex p.castSucc = Fin.natAdd (p.val + 1) r.succ := by
    apply Fin.ext
    simp only [parisiSplitLastIndex, Fin.val_natAdd, Fin.val_succ, r]
    omega
  rw [hi]
  unfold parisiInnerAuxSplitVars
  change Fin.append _ _ (Fin.natAdd (p.castSucc.val + 1) r.succ) = _
  rw [Fin.append_right]
  simp only [Fin.cons_succ, parisiQSuffixVars, Fin.val_castSucc]
  congr 1
  congr 1
  dsimp only [r]
  omega

/-- The two replica terminal marks are independent in the actual
coupling, even at the terminal outer insertion. -/
theorem gram_parisiSplit_terminal_coupling {k : ℕ} (p : Fin (k + 1)) (l l' : Fin 2) :
    gram (couplingFactorSgn 1 (p.val + 2) ((parisiSplitLastIndex p).val + 1)) l l' =
      if l = l' then 1 else 0 :=
  gram_couplingFactorSgn_of_le (by dsimp only [parisiSplitLastIndex]; omega) l l'

end SpinGlass
