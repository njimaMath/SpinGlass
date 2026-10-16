import SpinGlass.Parisi.Coupled.CoupledInnerFreeTrialComparison
import SpinGlass.Parisi.Coupled.CoupledOuterFreeTrialComparison

/-!
# Concrete free-mass trial witnesses

At the matching mass the fixed-trial value is the actual coupling
family. Its quadratic gain or the nonzero mass derivative selects a
positive continuous witness, including both ends of each split interval.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- Transport only the finite level count; the Gaussian site law is unchanged. -/
theorem randomFieldPairSiteY₀_cast {n m : ℕ} (e : n = m) (μh : Measure ℝ)
    (ns : Fin n → ℝ) (v₀ : ℝ≥0) (vs : Fin n → ℝ≥0) (lam : ℝ)
    (K₀ : Fin 2 → Fin 2 → ℝ) (K : Fin n → Fin 2 → Fin 2 → ℝ) :
    randomFieldPairSiteY₀ μh ns v₀ vs lam K₀ K =
      randomFieldPairSiteY₀ μh (fun i => ns (Fin.cast e.symm i)) v₀
        (fun i => vs (Fin.cast e.symm i)) lam K₀ (fun i => K (Fin.cast e.symm i)) := by
  subst m
  rfl

theorem parisiInnerFreeCoupledMasses_matching {k : ℕ} (ms : Fin k → ℝ) (p : Fin k) :
    parisiInnerFreeCoupledMasses ms p (ms p) = parisiSplitPhysicalMasses ms p.castSucc := by
  funext i
  rw [parisiInnerFreeCoupledMasses_apply, parisiSplitPhysicalMasses_apply]
  simp only [Fin.val_castSucc]
  by_cases hbefore : i.val < p.val + 1
  · rw [ite_eq_left hbefore, ite_eq_left hbefore]
  · rw [ite_eq_right hbefore, ite_eq_right hbefore]
    by_cases heq : i.val = p.val + 1
    · rw [ite_eq_left heq, heq, mExt_val_succ]
    · rw [ite_eq_right heq]

theorem parisiOuterFreeCoupledMasses_matching {k : ℕ} (ms : Fin k → ℝ) (p : Fin (k + 1)) :
    parisiOuterFreeCoupledMasses ms p (mExt ms (p.val + 1)) = parisiSplitPhysicalMasses ms p := by
  funext i
  rw [parisiOuterFreeCoupledMasses_apply, parisiSplitPhysicalMasses_apply]
  by_cases hbefore : i.val < p.val
  · rw [ite_eq_left hbefore, ite_eq_left (by omega)]
  · rw [ite_eq_right hbefore]
    by_cases heq : i.val = p.val
    · rw [ite_eq_left heq, ite_eq_left (by omega), heq]
    · rw [ite_eq_right heq, ite_eq_right (by omega)]

theorem parisiInnerFreeCouplingValue_matching (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (t v lam : ℝ) :
    parisiInnerFreeCouplingValue μh ξ ms qs p (t * (deriv ξ (qs p.succ) - deriv ξ v)) (ms p) lam =
      parisiInnerCouplingValue μh ξ ms qs p t v lam := by
  unfold parisiInnerFreeCouplingValue parisiInnerCouplingValue
  rw [parisiInnerFreeCoupledMasses_matching,
    randomFieldPairSiteY₀_cast (parisiSplitSize_eq p.castSucc).symm]
  congr 1 <;> funext i <;>
    simp [parisiSplitPhysicalMasses, parisiInnerFreeTotalVars, parisiSplitIndex]

theorem parisiOuterFreeCouplingValue_matching (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t v lam : ℝ) :
    parisiOuterFreeCouplingValue μh ξ ms qs p (t * (deriv ξ v - deriv ξ (qs p)))
      (mExt ms (p.val + 1)) lam = parisiOuterCouplingValue μh ξ ms qs p t v lam := by
  unfold parisiOuterFreeCouplingValue parisiOuterCouplingValue
  rw [parisiOuterFreeCoupledMasses_matching,
    randomFieldPairSiteY₀_cast (parisiSplitSize_eq p).symm]
  congr 1 <;> funext i <;>
    simp [parisiSplitPhysicalMasses, parisiOuterFreeTotalVars, parisiSplitIndex]

/-- The matching free-mass trial retains the concrete coupling square gain. -/
theorem parisiInnerFreeTrialGap_at_trial_ge_quadratic
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t v : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (qs p.castSucc) (qs p.succ)) :
    parisiRightResponseGap μh ξ ms qs p t v ^ 2 / 2 ≤
      parisiInnerFreeTrialGap μh ξ ms qs p v (ms p)
        (-(parisiRightResponseGap μh ξ ms qs p t v)) t v := by
  have hg := parisiInnerCouplingValue_le_gain hμ hξ ms qs p hm hq ht hv
  dsimp only at hg
  unfold parisiInnerFreeTrialGap
  rw [parisiInnerFreeCouplingValue_matching]
  simp only [parisiOverlapTangentDefect, sub_self, zero_mul, sub_zero, mul_zero, add_zero]
  unfold parisiInterpolationBracket parisiSplitBracket
  linarith

structure ParisiInnerFreeTrial {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (p : Fin k) where
  overlap : ℝ
  overlap_mem : overlap ∈ Icc (qs p.castSucc) (qs p.succ)
  mass : ℝ
  mass_mem : mass ∈ Icc (ms p / 2) (mExt ms (p.val + 2))
  coupling : ℝ

/-- The scalar coupling-or-mass alternative gives an actual admissible
fixed trial. Its positivity holds before any volume or Gaussian law is chosen. -/
theorem exists_parisiInnerFreeTrial_positive_gap_of_massResponse
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t v : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (qs p.castSucc) (qs p.succ))
    (hd : parisiRightResponseGap μh ξ ms qs p t v = 0 →
      parisiRightU μh ξ ms qs p (t * (deriv ξ (qs p.succ) - deriv ξ v)) -
        t * (parisiTheta ξ (qs p.succ) - parisiTheta ξ v) ≠ 0) :
    ∃ w : ParisiInnerFreeTrial ms qs p,
      0 < parisiInnerFreeTrialGap μh ξ ms qs p w.overlap w.mass w.coupling t v := by
  by_cases hz : parisiRightResponseGap μh ξ ms qs p t v = 0
  · obtain ⟨b, hb, hg⟩ := exists_parisiInnerFreeScalarBound_lt_of_deriv_ne_zero hμ hξ ms qs p hm hq ht hv (hd hz)
    have hb0 : 0 < b := by linarith [hm.2.1 p, hb.1]
    refine ⟨⟨v, hv, b, ⟨hb.1.le, hb.2.le⟩, 0⟩, ?_⟩
    change 0 < parisiInnerFreeTrialGap μh ξ ms qs p v b 0 t v
    rw [parisiInnerFreeTrialGap_at_trial_zero hμ ξ ms qs p hm hb0]
    exact sub_pos.2 hg
  · have hb : ms p ∈ Ioo (ms p / 2) (mExt ms (p.val + 2)) :=
      mem_of_mem_nhds (parisiInnerFreeMass_mem_nhds_matching ms p hm)
    refine ⟨⟨v, hv, ms p, ⟨hb.1.le, hb.2.le⟩, -(parisiRightResponseGap μh ξ ms qs p t v)⟩, ?_⟩
    exact (div_pos (sq_pos_of_ne_zero hz) (by norm_num)).trans_le
      (parisiInnerFreeTrialGap_at_trial_ge_quadratic hμ hξ ms qs p hm hq ht hv)

/-- The matching free-mass trial retains the concrete coupling square gain. -/
theorem parisiOuterFreeTrialGap_at_trial_ge_quadratic
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t v : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (qs p) (qExt qs (p.val + 2))) :
    parisiLeftResponseGap μh ξ ms qs p t v ^ 2 / 2 ≤
      parisiOuterFreeTrialGap μh ξ ms qs p v (mExt ms (p.val + 1))
        (-(parisiLeftResponseGap μh ξ ms qs p t v)) t v := by
  have hg := parisiOuterCouplingValue_le_gain hμ hξ ms qs p hm hq ht hv
  dsimp only at hg
  unfold parisiOuterFreeTrialGap
  rw [parisiOuterFreeCouplingValue_matching]
  simp only [parisiOverlapTangentDefect, sub_self, zero_mul, sub_zero, mul_zero, add_zero]
  unfold parisiInterpolationBracket parisiSplitBracket
  linarith

structure ParisiOuterFreeTrial {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (p : Fin (k + 1)) where
  overlap : ℝ
  overlap_mem : overlap ∈ Icc (qs p) (qExt qs (p.val + 2))
  mass : ℝ
  mass_mem : mass ∈ Icc (mExt ms p.val) (2 * mExt ms (p.val + 1))
  mass_pos : 0 < mass
  coupling : ℝ

/-- The scalar coupling-or-mass alternative gives an actual admissible
fixed trial. Its positivity holds before any volume or Gaussian law is chosen. -/
theorem exists_parisiOuterFreeTrial_positive_gap_of_massResponse
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t v : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (hd : parisiLeftResponseGap μh ξ ms qs p t v = 0 →
      parisiLeftU μh ξ ms qs p (t * (deriv ξ v - deriv ξ (qs p))) -
        t * (parisiTheta ξ v - parisiTheta ξ (qs p)) ≠ 0) :
    ∃ w : ParisiOuterFreeTrial ms qs p,
      0 < parisiOuterFreeTrialGap μh ξ ms qs p w.overlap w.mass w.coupling t v := by
  by_cases hz : parisiLeftResponseGap μh ξ ms qs p t v = 0
  · obtain ⟨b, hb, hg⟩ := exists_parisiOuterFreeScalarBound_lt_of_deriv_ne_zero hμ hξ ms qs p hm hq ht hv (hd hz)
    have hb0 : 0 < b := lt_of_le_of_lt (mExt_nonneg (fun i => (hm.2.1 i).le) _) hb.1
    refine ⟨⟨v, hv, b, ⟨hb.1.le, hb.2.le⟩, hb0, 0⟩, ?_⟩
    change 0 < parisiOuterFreeTrialGap μh ξ ms qs p v b 0 t v
    rw [parisiOuterFreeTrialGap_at_trial_zero hμ ξ ms qs p hm hb0]
    exact sub_pos.2 hg
  · have hb : mExt ms (p.val + 1) ∈ Ioo (mExt ms p.val) (2 * mExt ms (p.val + 1)) :=
      mem_of_mem_nhds (parisiOuterFreeMass_mem_nhds_matching ms p hm)
    refine ⟨⟨v, hv, mExt ms (p.val + 1), ⟨hb.1.le, hb.2.le⟩, hm.mExt_pos (by omega), -(parisiLeftResponseGap μh ξ ms qs p t v)⟩, ?_⟩
    exact (div_pos (sq_pos_of_ne_zero hz) (by norm_num)).trans_le
      (parisiOuterFreeTrialGap_at_trial_ge_quadratic hμ hξ ms qs p hm hq ht hv)

theorem ParisiInnerFreeTrial.mass_pos {k : ℕ} {ms : Fin k → ℝ}
    {qs : Fin (k + 1) → ℝ} {p : Fin k} (w : ParisiInnerFreeTrial ms qs p)
    (hm : ParisiMAdmissible ms) : 0 < w.mass := by
  linarith [hm.2.1 p, w.mass_mem.1]

/-- Select the MIN tolerance before its parameters. Every far inner
point then has a positive continuous physical scalar trial witness. -/
theorem exists_uniform_parisiInnerFreeTrial_positive_far_gap
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {t₀ ρ : ℝ}
    (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ {μh : Measure ℝ} [IsProbabilityMeasure μh], Integrable id μh →
      ∀ {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → ParisiQAdmissible qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ p : Fin k, ∀ t ∈ Icc (0 : ℝ) t₀, ∀ v ∈ Icc (qs p.castSucc) (qs p.succ),
      ρ ≤ qs p.succ - v → ∃ w : ParisiInnerFreeTrial ms qs p,
        0 < parisiInnerFreeTrialGap μh ξ ms qs p w.overlap w.mass w.coupling t v := by
  obtain ⟨ε, hε, η, hη, hd⟩ := exists_uniform_inner_massResponse_pos_of_coupling_eq_zero hξ ht₀ hρ
  refine ⟨ε, hε, ?_⟩
  intro μh _ hμ k ms qs hm hq hfull hnear p t ht v hv hdist
  apply exists_parisiInnerFreeTrial_positive_gap_of_massResponse hμ hξ ms qs p hm hq
    ⟨ht.1, ht.2.trans ht₀.2.le⟩ hv
  intro hz
  exact ne_of_gt (hη.trans_le (hd hμ ms qs hm hq hfull hnear p t ht v hv hdist hz))

/-- Select the MIN tolerance before its parameters. Every far outer
point then has a positive continuous physical scalar trial witness. -/
theorem exists_uniform_parisiOuterFreeTrial_positive_far_gap
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {t₀ ρ : ℝ}
    (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ {μh : Measure ℝ} [IsProbabilityMeasure μh], Integrable id μh →
      ∀ {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → ParisiQAdmissible qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ p : Fin (k + 1), ∀ t ∈ Icc (0 : ℝ) t₀, ∀ v ∈ Icc (qs p) (qExt qs (p.val + 2)),
      ρ ≤ v - qs p → ∃ w : ParisiOuterFreeTrial ms qs p,
        0 < parisiOuterFreeTrialGap μh ξ ms qs p w.overlap w.mass w.coupling t v := by
  obtain ⟨ε, hε, η, hη, hd⟩ := exists_uniform_outer_massResponse_neg_of_coupling_eq_zero hξ ht₀ hρ
  refine ⟨ε, hε, ?_⟩
  intro μh _ hμ k ms qs hm hq hfull hnear p t ht v hv hdist
  apply exists_parisiOuterFreeTrial_positive_gap_of_massResponse hμ hξ ms qs p hm hq
    ⟨ht.1, ht.2.trans ht₀.2.le⟩ hv
  intro hz
  exact by
    have hh := hd hμ ms qs hm hq hfull hnear p t ht v hv hdist hz
    intro he
    rw [he] at hh
    linarith

end SpinGlass
