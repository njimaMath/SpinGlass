import SpinGlass.Parisi.Coupled.CoupledRootMassLimit

/-!
# Driven and auxiliary Gaussian witnesses in the initial interval

For a nonnegative constrained overlap u below q₁, the driven root variance
is t(ξ'(u)−ξ'(0)). The auxiliary root retains (1−t)(ξ'(q₁)−ξ'(0)); the
new positive-mass level has zero auxiliary variance. The total law is the
root response law used in the proved zero inserted-mass limit.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

noncomputable def parisiRootDrivenRootVar (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (t u : ℝ) : ℝ≥0 :=
  t.toNNReal * parisiVar ξ (splitParisiRootOverlap qs u) 0

noncomputable def parisiRootDrivenVars (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (t u : ℝ) : Fin (k + 2) → ℝ≥0 :=
  fun i => t.toNNReal * parisiVar ξ (splitParisiRootOverlap qs u) (i.val + 1)

noncomputable def parisiRootAuxVars (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (t : ℝ) : Fin (k + 2) → ℝ≥0 :=
  Fin.cons 0 (fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i)

def parisiRootCouplingRho {k : ℕ} (qs : Fin (k + 1) → ℝ) (u : ℝ) :
    Fin 2 → Fin 2 → ℕ → ℝ := couplingRhoSgn (qExt (splitParisiRootOverlap qs u)) 1 1

theorem parisiRootOverlap_mem_domain_of_admissible {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (qs 0)) :
    splitParisiRootOverlap qs u ∈ parisiOverlapDomain (k + 1) :=
  splitParisiRootOverlap_mem_domain
    (mem_parisiOverlapDomain_iff.2 ⟨hq.monotone, hq.2.1, hq.2.2⟩) hu

/-- The driven inner root piece stays within the old nonnegative
root variance, including time zero and both overlap endpoints. -/
theorem parisi_root_time_variance_mem_Icc {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) (qs 0)) :
    t * (deriv ξ (qs 0) - deriv ξ u) ∈ Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0) := by
  have hdelta := mapsTo_parisi_variance_coordinate hξ
    (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (hq.mem_Icc 0) hu
  have hnonneg : 0 ≤ t * (deriv ξ (qs 0) - deriv ξ u) := mul_nonneg ht.1 hdelta.1
  refine ⟨hnonneg, ?_⟩
  nlinarith [hdelta.2, mul_nonneg (sub_nonneg.2 ht.2) hdelta.1]

theorem parisiVar_splitParisiRootOverlap_root (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (u : ℝ) :
    parisiVar ξ (splitParisiRootOverlap qs u) 0 = (deriv ξ u - deriv ξ 0).toNNReal := by
  simp only [parisiVar, qExt_zero, qExt_succ_of_lt _ (by omega : 0 < k + 2),
    splitParisiRootOverlap]
  rfl

theorem parisiVar_splitParisiRootOverlap_first (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (u : ℝ) :
    parisiVar ξ (splitParisiRootOverlap qs u) 1 = (deriv ξ (qs 0) - deriv ξ u).toNNReal := by
  unfold parisiVar
  rw [qExt_splitParisiRootOverlap_succ qs u 0, qExt_succ_of_lt qs (Nat.succ_pos k),
    qExt_succ_of_lt _ (by omega : 0 < k + 2)]
  rfl

/-- The total root law is the old root variance minus the driven
inner piece, with clamping justified on the actual closed interval. -/
theorem parisiRootDrivenRootVar_add_aux_eq {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) (qs 0)) :
    parisiRootDrivenRootVar ξ qs t u + parisiAuxRootVar ξ qs t =
      (deriv ξ (qs 0) - deriv ξ 0 - t * (deriv ξ (qs 0) - deriv ξ u)).toNNReal := by
  have humem : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans (hq.mem_Icc 0).2⟩
  have hx : 0 ≤ deriv ξ u - deriv ξ 0 := sub_nonneg.2
    (hξ.strictMonoOn_deriv.monotoneOn (by norm_num) humem hu.1)
  have ha : 0 ≤ deriv ξ (qs 0) - deriv ξ 0 := sub_nonneg.2
    (hξ.strictMonoOn_deriv.monotoneOn (by norm_num) (hq.mem_Icc 0) hq.2.1)
  have hv := parisi_root_time_variance_mem_Icc hξ qs hq ht hu
  have hvar : parisiVar ξ qs 0 = (deriv ξ (qs 0) - deriv ξ 0).toNNReal := by
    simp only [parisiVar, qExt_zero, qExt_succ_of_lt qs (Nat.succ_pos k)]
    rfl
  unfold parisiRootDrivenRootVar parisiAuxRootVar
  rw [parisiVar_splitParisiRootOverlap_root, hvar]
  apply NNReal.eq
  simp only [NNReal.coe_add, NNReal.coe_mul, Real.coe_toNNReal _ ht.1,
    Real.coe_toNNReal _ (sub_nonneg.2 ht.2), Real.coe_toNNReal _ hx,
    Real.coe_toNNReal _ ha, Real.coe_toNNReal _ (sub_nonneg.2 hv.2)]
  ring

/-- All positive-mass total variances are exactly the root response
list, with zero auxiliary variance on the newly inserted level. -/
theorem parisiRootDrivenVars_add_aux_eq (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : ℝ) :
    (fun i => parisiRootDrivenVars ξ qs t u i + parisiRootAuxVars ξ qs t i) =
      parisiRootResponseVars ξ qs (t * (deriv ξ (qs 0) - deriv ξ u)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [parisiRootDrivenVars, parisiRootAuxVars, parisiRootResponseVars, Fin.val_zero,
      Fin.cons_zero, zero_add, add_zero, parisiVar_splitParisiRootOverlap_first]
    exact (Real.toNNReal_mul ht.1).symm
  · simp only [parisiRootDrivenVars, parisiRootAuxVars, parisiRootResponseVars, Fin.val_succ,
      Fin.cons_succ, parisiLevelVars]
    rw [show j.val + 1 + 1 = j.val + 2 by omega,
      parisiVar_splitParisiRootOverlap_after, nnreal_time_split_sum ht]

theorem parisiRootDrivenRootVar_mul_gram {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : 0 ≤ t) (hu : u ∈ Icc (0 : ℝ) (qs 0)) (l l' : Fin 2) :
    (parisiRootDrivenRootVar ξ qs t u : ℝ) * gram (couplingFactorSgn 1 1 0) l l' =
      deriv (parisiTimeProfile ξ t) (parisiRootCouplingRho qs u l l' 1) -
        deriv (parisiTimeProfile ξ t) (parisiRootCouplingRho qs u l l' 0) := by
  have he : parisiRootDrivenRootVar ξ qs t u =
      couplingVar (parisiTimeProfile ξ t) (qExt (splitParisiRootOverlap qs u)) 0 := by
    change t.toNNReal * parisiVar ξ (splitParisiRootOverlap qs u) 0 =
      parisiVar (parisiTimeProfile ξ t) (splitParisiRootOverlap qs u) 0
    exact (parisiVar_timeProfile ξ _ ht 0).symm
  rw [he]
  unfold parisiRootCouplingRho
  have hh := couplingVar_mul_gram (J'' := Fin 2) (τ := 1)
    (by norm_num : (1 : ℝ) ^ 2 = 1) (fun x => by simp only [one_mul])
    (parisiTimeProfile_deriv_qExt_le_succ hξ (parisiRootOverlap_mem_domain_of_admissible qs hq hu) ht 0) l l'
  simpa only [gram_sumL, zero_add] using hh

theorem parisiRootDrivenVars_mul_gram {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : 0 ≤ t) (hu : u ∈ Icc (0 : ℝ) (qs 0)) (i : Fin (k + 2)) (l l' : Fin 2) :
    (parisiRootDrivenVars ξ qs t u i : ℝ) * gram (couplingFactorSgn 1 1 (i.val + 1)) l l' =
      deriv (parisiTimeProfile ξ t) (parisiRootCouplingRho qs u l l' (i.val + 2)) -
        deriv (parisiTimeProfile ξ t) (parisiRootCouplingRho qs u l l' (i.val + 1)) := by
  have he : parisiRootDrivenVars ξ qs t u i =
      couplingVar (parisiTimeProfile ξ t) (qExt (splitParisiRootOverlap qs u)) (i.val + 1) := by
    change t.toNNReal * parisiVar ξ (splitParisiRootOverlap qs u) (i.val + 1) =
      parisiVar (parisiTimeProfile ξ t) (splitParisiRootOverlap qs u) (i.val + 1)
    exact (parisiVar_timeProfile ξ _ ht _).symm
  rw [he]
  unfold parisiRootCouplingRho
  have hh := couplingVar_mul_gram (J'' := Fin 2) (τ := 1)
    (by norm_num : (1 : ℝ) ^ 2 = 1) (fun x => by simp only [one_mul])
    (parisiTimeProfile_deriv_qExt_le_succ hξ
      (parisiRootOverlap_mem_domain_of_admissible qs hq hu) ht (i.val + 1)) l l'
  simpa only [gram_sumL, show i.val + 1 + 1 = i.val + 2 by omega] using hh

theorem parisiRootCouplingRho_zero {k : ℕ} (qs : Fin (k + 1) → ℝ) (u : ℝ) (l l' : Fin 2) :
    parisiRootCouplingRho qs u l l' 0 = 0 := couplingRhoSgn_zero _ (qExt_zero _) 1 1 l l'

theorem parisiRootCouplingRho_mem_Icc {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (hq : ParisiQAdmissible qs) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (qs 0)) (l l' : Fin 2) (r : ℕ) :
    parisiRootCouplingRho qs u l l' r ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hmono, hzero, hone⟩ := mem_parisiOverlapDomain_iff.1
    (parisiRootOverlap_mem_domain_of_admissible qs hq hu)
  unfold parisiRootCouplingRho couplingRhoSgn
  split_ifs
  · exact qExt_mem_Icc hmono hzero hone r
  · simpa only [one_mul] using qExt_mem_Icc hmono hzero hone (min r 1)

theorem parisiRootCouplingRho_top {k : ℕ} (qs : Fin (k + 1) → ℝ) (u : ℝ) (l l' : Fin 2) :
    parisiRootCouplingRho qs u l l' (k + 3) = if l = l' then 1 else u := by
  have hh := couplingRhoSgn_top (qExt (splitParisiRootOverlap qs u)) 1
    (τ := 1) (κ := k + 2) (by omega) (qExt_of_le _ (by omega)) l l'
  unfold parisiRootCouplingRho
  have hfirst : qExt (splitParisiRootOverlap qs u) 1 = u := by
    rw [qExt_succ_of_lt _ (by omega : 0 < k + 2)]
    rfl
  simpa only [one_mul, hfirst, show k + 2 + 1 = k + 3 by omega] using hh

theorem pairDiagDefect_parisiRootCouplingRho_top (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (u : ℝ) :
    pairDiagDefect ξ u (fun l l' => parisiRootCouplingRho qs u l l' (k + 3)) = 0 := by
  have he : (fun l l' => parisiRootCouplingRho qs u l l' (k + 3)) =
      fun l l' => if l = l' then (1 : ℝ) else u :=
    funext fun l => funext fun l' => parisiRootCouplingRho_top qs u l l'
  rw [he, pairDiagDefect_diag]

/-- The positive root insertion adds only its actual first-interval
mass correction to the old weighted theta sum. -/
theorem parisiRootResponseMasses_correction_eq (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (u m : ℝ) :
    (∑ i : Fin (k + 2), parisiRootResponseMasses ms m i *
      (parisiTheta ξ (qExt (splitParisiRootOverlap qs u) (i.val + 2)) -
        parisiTheta ξ (qExt (splitParisiRootOverlap qs u) (i.val + 1)))) =
      parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ u) := by
  rw [Fin.sum_univ_succ]
  simp only [parisiRootResponseMasses, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    zero_add, Fin.val_succ]
  have hfirst : qExt (splitParisiRootOverlap qs u) 1 = u := by
    rw [qExt_succ_of_lt _ (by omega : 0 < k + 2)]
    rfl
  rw [qExt_splitParisiRootOverlap_succ qs u 0, qExt_succ_of_lt qs (Nat.succ_pos k), hfirst]
  have htail : (∑ i : Fin (k + 1), parisiLevelMasses ms i *
      (parisiTheta ξ (qExt (splitParisiRootOverlap qs u) (i.val + 1 + 2)) -
        parisiTheta ξ (qExt (splitParisiRootOverlap qs u) (i.val + 1 + 1)))) =
      parisiCorrection ξ ms qs := by
    unfold parisiCorrection
    apply Finset.sum_congr rfl
    intro i _
    rw [qExt_splitParisiRootOverlap_succ qs u (i.val + 1),
      show i.val + 1 + 1 = i.val + 2 by omega, qExt_splitParisiRootOverlap_succ qs u i.val,
      parisiLevelMasses_apply]
  rw [htail]
  change m * (parisiTheta ξ (qs 0) - parisiTheta ξ u) + parisiCorrection ξ ms qs = _
  ring

/-- The exact driven coupled correction at positive root mass. Its
additional term tends to zero with the inserted mass. -/
theorem coupledLevelSum_parisiRoot_eq_correction (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u m : ℝ) :
    (1 / 2) * coupledLevelSum (parisiTimeProfile ξ t) (parisiRootCouplingRho qs u)
      (parisiRootResponseMasses ms m) =
      t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ u)) := by
  unfold parisiRootCouplingRho
  rw [coupledLevelSum_couplingRhoSgn (fun x => by simp only [one_mul])]
  have hh := couplingLevelSum_halveBelow (parisiTimeProfile ξ t)
    (qExt (splitParisiRootOverlap qs u)) (τ := 1) (by norm_num) (parisiRootResponseMasses ms m)
  simp only [Nat.sub_self, halveBelow_zero] at hh
  rw [hh]
  simp_rw [parisiTheta_timeProfile]
  have he : (∑ i : Fin (k + 2), parisiRootResponseMasses ms m i *
      (t * parisiTheta ξ (qExt (splitParisiRootOverlap qs u) (i.val + 2)) -
        t * parisiTheta ξ (qExt (splitParisiRootOverlap qs u) (i.val + 1)))) =
      t * (∑ i : Fin (k + 2), parisiRootResponseMasses ms m i *
        (parisiTheta ξ (qExt (splitParisiRootOverlap qs u) (i.val + 2)) -
          parisiTheta ξ (qExt (splitParisiRootOverlap qs u) (i.val + 1)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, parisiRootResponseMasses_correction_eq]
  ring

/-- The positive inserted root level has a deterministic auxiliary
mark, so the actual physical cascade is the original one for every mass. -/
theorem cascadeRec_parisi_root_aux_eq {N k : ℕ} (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t : ℝ) {m : ℝ} (hm0 : 0 < m)
    (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (z₀ : Fin N × Fin 2 → ℝ) :
    cascadeRec (k + 2) (parisiRootResponseMasses ms m)
        (siteGaussianMarks (Fin N × Fin 2) _ (parisiRootAuxVars ξ qs t))
        (pairHamG N _ c H lam a (couplingFactorSgn 1 1 0)
          (fun i => couplingFactorSgn 1 1 (i.val + 1)) z₀) =
      cascadeRec (k + 1) (parisiLevelMasses ms)
        (siteGaussianMarks (Fin N × Fin 2) _ (fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i))
        (pairHamG N _ c H lam a (couplingFactorSgn 1 1 0)
          (fun i => couplingFactorSgn 1 1 (i.val + 1)) z₀) := by
  have hmass : parisiRootResponseMasses ms m 0 ≠ 0 := hm0.ne'
  have hv : parisiRootAuxVars ξ qs t 0 = 0 := rfl
  rw [cascadeRec_pairHamG_remove_zero_eq _ _ 0 hmass hv, Fin.removeNth_zero,
    Fin.removeNth_zero, Fin.removeNth_zero]
  simp only [parisiRootResponseMasses, parisiRootAuxVars, Fin.tail_cons]
  have hK : Fin.tail (fun i : Fin (k + 2) => couplingFactorSgn 1 1 (i.val + 1)) =
      fun i : Fin (k + 1) => couplingFactorSgn 1 1 (i.val + 1) := by
    funext i
    simp only [Fin.tail, Fin.val_succ, couplingFactorSgn,
      ite_eq_right (by omega : ¬ i.val + 1 + 1 < 1),
      ite_eq_right (by omega : ¬ i.val + 1 < 1)]
  rw [hK]

end SpinGlass
