import SpinGlass.Parisi.ParisiMin
import SpinGlass.Parisi.ParisiMassContinuity
import SpinGlass.Parisi.ParisiLevelReduction

/-!
# Closed parameter domain for Talagrand's MIN condition

The fixed-level minimization in Lemma 14.5.5 takes place on nondecreasing
mass and overlap lists. At mass zero the original cascade expression is
replaced by its Cole-Hopf extension, which is the Gaussian expectation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

set_option maxHeartbeats 1000000

/-- The closed mass domain $0 \le m_1 \le \cdots \le m_k \le 1$. -/
def parisiMassDomain (k : ℕ) : Set (Fin k → ℝ) :=
  Set.pi Set.univ (fun _ => Icc (0 : ℝ) 1) ∩ {ms | Monotone ms}

theorem mem_parisiMassDomain_iff {k : ℕ} {ms : Fin k → ℝ} :
    ms ∈ parisiMassDomain k ↔
      Monotone ms ∧ (∀ i, 0 ≤ ms i) ∧ ∀ i, ms i ≤ 1 := by
  simp only [parisiMassDomain, mem_inter_iff, mem_pi, mem_univ, forall_true_left,
    mem_Icc]
  constructor
  · rintro ⟨hb, hm⟩
    exact ⟨hm, (fun i => (hb i).1), (fun i => (hb i).2)⟩
  · rintro ⟨hm, h0, h1⟩
    exact ⟨(fun i => ⟨h0 i, h1 i⟩), hm⟩

theorem isCompact_parisiMassDomain (k : ℕ) : IsCompact (parisiMassDomain k) :=
  (isCompact_univ_pi (fun _ : Fin k => isCompact_Icc)).inter_right isClosed_monotone

theorem parisiMassDomain_nonempty (k : ℕ) : (parisiMassDomain k).Nonempty := by
  refine ⟨fun _ => 0, mem_parisiMassDomain_iff.2 ?_⟩
  exact ⟨monotone_const, (fun _ => le_refl _), (fun _ => zero_le_one)⟩

/-- The compact domain for fixed $k$, including repeated levels and endpoint masses. -/
def parisiParameterDomain (k : ℕ) :
    Set ((Fin k → ℝ) × (Fin (k + 1) → ℝ)) :=
  (parisiMassDomain k).prod (parisiOverlapDomain k)

theorem mem_parisiParameterDomain_iff {k : ℕ}
    {p : (Fin k → ℝ) × (Fin (k + 1) → ℝ)} :
    p ∈ parisiParameterDomain k ↔
      p.1 ∈ parisiMassDomain k ∧ p.2 ∈ parisiOverlapDomain k :=
  Iff.rfl

theorem isCompact_parisiParameterDomain (k : ℕ) :
    IsCompact (parisiParameterDomain k) :=
  (isCompact_parisiMassDomain k).prod (isCompact_parisiOverlapDomain k)

theorem parisiParameterDomain_nonempty (k : ℕ) :
    (parisiParameterDomain k).Nonempty := by
  obtain ⟨ms, hms⟩ := parisiMassDomain_nonempty k
  obtain ⟨qs, hqs⟩ := parisiOverlapDomain_nonempty k
  exact ⟨(ms, qs), ⟨hms, hqs⟩⟩

/-- The Cole-Hopf extension of the root recursion, valid when a mass is zero. -/
noncomputable def closedParisiX₀ (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) : ℝ :=
  coleHopfIterate (k + 2) (Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms))
    (parisiAllVars ξ qs) (parisiLogCoshTerminal h) 0

theorem closedParisiX₀_eq_parisiX₀ {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (h : ℝ) :
    closedParisiX₀ ξ ms qs h = parisiX₀ ξ ms qs (parisiLogCoshTerminal h) := by
  exact (parisiX₀_eq_coleHopfIterate_all ms qs hm h).symm

/-- The extended random-field functional agrees with the original on strict masses. -/
noncomputable def closedRandomFieldParisiFunctional
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) : ℝ :=
  Real.log 2 + (∫ h, closedParisiX₀ ξ ms qs h ∂μh)
    - (1 / 2) * ∑ p ∈ Finset.range (k + 1),
        mExt ms (p + 1) *
          (parisiTheta ξ (qExt qs (p + 2)) - parisiTheta ξ (qExt qs (p + 1)))

theorem closedRandomFieldParisiFunctional_eq
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) :
    closedRandomFieldParisiFunctional μh ξ ms qs =
      randomFieldParisiFunctional μh ξ ms qs := by
  unfold closedRandomFieldParisiFunctional randomFieldParisiFunctional randomFieldParisiX₀
  congr 1
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (closedParisiX₀_eq_parisiX₀ ms qs hm)

theorem continuous_mExt_parameter {k : ℕ} (r : ℕ) :
    Continuous (fun ms : Fin k → ℝ => mExt ms r) := by
  unfold mExt
  split_ifs
  · exact continuous_const
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_parisiAllMasses_parameter {k : ℕ} :
    Continuous (fun ms : Fin k → ℝ =>
      Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ ?_ i
  · exact continuous_const
  · intro j
    simpa only [Fin.cons_succ, parisiLevelMasses_apply] using
      (continuous_mExt_parameter (k := k) (j.val + 1))

theorem continuousOn_parisiAllVars_overlapCube {ξ : ℝ → ℝ} {k : ℕ}
    (hξ : TalagrandXiCondition ξ) :
    ContinuousOn (fun qs => parisiAllVars ξ qs) (parisiOverlapCube k) := by
  apply continuousOn_pi.2
  intro i
  have hd (r : ℕ) : ContinuousOn
      (fun qs : Fin (k + 1) → ℝ => deriv ξ (qExt qs r)) (parisiOverlapCube k) :=
    hξ.deriv_continuous.comp (continuous_qExt_local r).continuousOn
      (fun qs hq => qExt_mem_Icc_of_mem_cube hq r)
  exact continuous_real_toNNReal.comp_continuousOn
    ((hd (i.val + 1)).sub (hd i.val))

/-- The extended root recursion is jointly continuous in all closed parameters. -/
theorem continuousOn_closedParisiX₀_parameters
    {ξ : ℝ → ℝ} {k : ℕ} (hξ : TalagrandXiCondition ξ) (h : ℝ) :
    ContinuousOn (fun p : (Fin k → ℝ) × (Fin (k + 1) → ℝ) =>
      closedParisiX₀ ξ p.1 p.2 h) (parisiParameterDomain k) := by
  have hmc : ContinuousOn
      (fun p : (Fin k → ℝ) × (Fin (k + 1) → ℝ) =>
        Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses p.1))
      (parisiParameterDomain k) :=
    ((continuous_parisiAllMasses_parameter (k := k)).comp continuous_fst).continuousOn
  have hvc : ContinuousOn
      (fun p : (Fin k → ℝ) × (Fin (k + 1) → ℝ) => parisiAllVars ξ p.2)
      (parisiParameterDomain k) :=
    (continuousOn_parisiAllVars_overlapCube hξ).comp continuous_snd.continuousOn
      (fun _ hp => hp.2.1)
  have hm : ∀ p ∈ parisiParameterDomain k, ∀ i,
      Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses p.1) i ∈ Icc (0 : ℝ) 1 := by
    intro p hp i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j
      rw [Fin.cons_succ, parisiLevelMasses_apply]
      exact ⟨mExt_nonneg (mem_parisiMassDomain_iff.1 hp.1).2.1 _,
        mExt_le_one (mem_parisiMassDomain_iff.1 hp.1).2.2 _⟩
  have hc := continuousOn_coleHopfIterate_parameters_local
    (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal h))
    (fun x y => by simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le h x y)
    zero_le_one hmc hvc hm 0
  simpa only [closedParisiX₀] using hc

theorem closedParisiX₀_translate (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) :
    closedParisiX₀ ξ ms qs h =
      coleHopfIterate (k + 2) (Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms))
        (parisiAllVars ξ qs) (parisiLogCoshTerminal 0) h := by
  have ht : parisiLogCoshTerminal h =
      fun y => parisiLogCoshTerminal 0 (h + y) := by
    funext y
    simp only [parisiLogCoshTerminal, zero_add]
  unfold closedParisiX₀
  rw [ht]
  simpa only [add_zero] using
    coleHopfIterate_translate (Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms))
      (parisiAllVars ξ qs) (parisiLogCoshTerminal 0) h 0

theorem abs_closedParisiX₀_sub_field_le (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (h h' : ℝ) :
    |closedParisiX₀ ξ ms qs h' - closedParisiX₀ ξ ms qs h| ≤ |h' - h| := by
  rw [closedParisiX₀_translate, closedParisiX₀_translate]
  simpa only [one_mul] using
    abs_coleHopfIterate_sub_le (L := 1) (k + 2)
      (Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms))
      (parisiAllVars ξ qs)
      (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0))
      (fun x y => by simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0 x y)
      h h'

theorem continuous_closedParisiX₀_field (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    Continuous (fun h => closedParisiX₀ ξ ms qs h) :=
  (LipschitzWith.of_dist_le_mul (K := 1) (fun h h' => by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, abs_sub_comm] using
      abs_closedParisiX₀_sub_field_le ξ ms qs h h')).continuous

/-- The quenched expectation is continuous on the compact parameter domain.
The uniform domination uses only a first moment of the site field. -/
theorem continuousOn_closedRandomFieldParisiX₀_parameters
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ) :
    ContinuousOn (fun p : (Fin k → ℝ) × (Fin (k + 1) → ℝ) =>
      ∫ h, closedParisiX₀ ξ p.1 p.2 h ∂μh) (parisiParameterDomain k) := by
  obtain ⟨c, hc⟩ := (isCompact_parisiParameterDomain k).bddAbove_image
    ((continuousOn_closedParisiX₀_parameters (k := k) hξ 0).abs)
  have hbound : ∀ p ∈ parisiParameterDomain k, ∀ h,
      |closedParisiX₀ ξ p.1 p.2 h| ≤ max c 0 + |h| := by
    intro p hp h
    have h0 : |closedParisiX₀ ξ p.1 p.2 0| ≤ max c 0 :=
      (hc (mem_image_of_mem _ hp)).trans (le_max_left _ _)
    have hh := abs_closedParisiX₀_sub_field_le ξ p.1 p.2 0 h
    calc
      _ ≤ |closedParisiX₀ ξ p.1 p.2 h - closedParisiX₀ ξ p.1 p.2 0| +
          |closedParisiX₀ ξ p.1 p.2 0| := by
        simpa using abs_add_le
          (closedParisiX₀ ξ p.1 p.2 h - closedParisiX₀ ξ p.1 p.2 0)
          (closedParisiX₀ ξ p.1 p.2 0)
      _ ≤ _ := by simpa only [sub_zero, add_comm] using add_le_add hh h0
  have hbi : Integrable (fun h : ℝ => max c 0 + |h|) μh := by
    exact (integrable_const _).add (by simpa only [Real.norm_eq_abs, id_eq] using hμ.norm)
  refine continuousOn_of_dominated (bound := fun h : ℝ => max c 0 + |h|)
    (fun p _ => (continuous_closedParisiX₀_field ξ p.1 p.2).measurable.aestronglyMeasurable)
    ?_ hbi ?_
  · intro p hp
    exact Filter.Eventually.of_forall (fun h => by
      rw [Real.norm_eq_abs]
      exact hbound p hp h)
  · exact Filter.Eventually.of_forall (fun h =>
      continuousOn_closedParisiX₀_parameters hξ h)

/-- Joint continuity of the extended fixed-level Parisi functional. -/
theorem continuousOn_closedRandomFieldParisiFunctional_parameters
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ) :
    ContinuousOn (fun p : (Fin k → ℝ) × (Fin (k + 1) → ℝ) =>
      closedRandomFieldParisiFunctional μh ξ p.1 p.2)
      (parisiParameterDomain k) := by
  have htheta : ContinuousOn (parisiTheta ξ) (Icc (0 : ℝ) 1) :=
    (continuousOn_id.mul hξ.deriv_continuous).sub
      (fun x hx => (hξ.hasDeriv x hx).continuousAt.continuousWithinAt)
  have ht (r : ℕ) : ContinuousOn
      (fun p : (Fin k → ℝ) × (Fin (k + 1) → ℝ) =>
        parisiTheta ξ (qExt p.2 r)) (parisiParameterDomain k) :=
    htheta.comp (((continuous_qExt_local r).comp continuous_snd).continuousOn)
      (fun p hp => qExt_mem_Icc_of_mem_cube hp.2.1 r)
  have hm (r : ℕ) : ContinuousOn
      (fun p : (Fin k → ℝ) × (Fin (k + 1) → ℝ) => mExt p.1 r)
      (parisiParameterDomain k) :=
    ((continuous_mExt_parameter r).comp continuous_fst).continuousOn
  unfold closedRandomFieldParisiFunctional
  exact (continuousOn_const.add
    (continuousOn_closedRandomFieldParisiX₀_parameters hμ hξ)).sub
    (continuousOn_const.mul (continuousOn_finsetSum _ fun p _ =>
      (hm (p + 1)).mul ((ht (p + 2)).sub (ht (p + 1)))))

attribute [irreducible] closedRandomFieldParisiFunctional

/-- Compactness gives a true minimum at each fixed level count. -/
theorem exists_closedRandomFieldParisiMinimum_of_fixed_levels
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (k : ℕ)
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ) :
    ∃ p ∈ parisiParameterDomain k,
      IsMinOn (fun p => closedRandomFieldParisiFunctional μh ξ p.1 p.2)
        (parisiParameterDomain k) p := by
  let f : ((Fin k → ℝ) × (Fin (k + 1) → ℝ)) → ℝ :=
    fun p => closedRandomFieldParisiFunctional μh ξ p.1 p.2
  have hc : ContinuousOn f (parisiParameterDomain k) :=
    continuousOn_closedRandomFieldParisiFunctional_parameters hμ hξ
  obtain ⟨p, hp, hmin⟩ := (isCompact_parisiParameterDomain k).exists_isMinOn
    (parisiParameterDomain_nonempty k) hc
  exact ⟨p, hp, hmin⟩

/-- The compact minimum at a selected level count remains near the global infimum. -/
theorem exists_nearOptimal_closedRandomFieldParisiMinimum
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (p : (Fin k → ℝ) × (Fin (k + 1) → ℝ)),
      p ∈ parisiParameterDomain k ∧
      closedRandomFieldParisiFunctional μh ξ p.1 p.2 <
        randomFieldParisiInf μh ξ + ε ∧
      IsMinOn (fun p => closedRandomFieldParisiFunctional μh ξ p.1 p.2)
        (parisiParameterDomain k) p := by
  obtain ⟨k, ms₀, qs₀, hsm, hpos, hlt, hmono, hq0, hq1, hnear⟩ :=
    exists_randomFieldParisiFunctional_lt_inf_add_of_talagrand μh hξ hε
  have hm₀ : ParisiMAdmissible ms₀ := ⟨hsm, hpos, hlt⟩
  have hp₀ : (ms₀, qs₀) ∈ parisiParameterDomain k := by
    refine ⟨mem_parisiMassDomain_iff.2 ?_, mem_parisiOverlapDomain_iff.2 ?_⟩
    · exact ⟨hsm.monotone, (fun i => (hpos i).le), (fun i => (hlt i).le)⟩
    · exact ⟨hmono, hq0, hq1⟩
  obtain ⟨p, hp, hmin⟩ :=
    exists_closedRandomFieldParisiMinimum_of_fixed_levels k hμ hξ
  refine ⟨k, p, hp, ?_, hmin⟩
  calc
    closedRandomFieldParisiFunctional μh ξ p.1 p.2 ≤
        closedRandomFieldParisiFunctional μh ξ ms₀ qs₀ := hmin hp₀
    _ = randomFieldParisiFunctional μh ξ ms₀ qs₀ :=
      closedRandomFieldParisiFunctional_eq μh ξ ms₀ qs₀ hm₀
    _ < _ := hnear

/-- Removing a repeated overlap preserves the extended recursion even when
some mass vanishes. -/
theorem closedParisiX₀_erase_adjacent_eq {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin (k + 1) → ℝ) (qs : Fin (k + 2) → ℝ)
    (p : Fin (k + 1)) (hq : qs p.castSucc = qs p.succ) (h : ℝ) :
    closedParisiX₀ ξ (eraseParisiMass ms p) (eraseParisiOverlap qs p) h =
      closedParisiX₀ ξ ms qs h := by
  unfold closedParisiX₀
  rw [parisiAllMasses_eraseParisiMass, parisiAllVars_eraseParisiOverlap qs p hq]
  have hz : parisiAllVars ξ qs p.castSucc.succ = 0 :=
    parisiVar_eq_zero_of_adjacent_eq qs p hq
  rw [coleHopfIterate_erase_zero_var (k + 2) _ _ p.castSucc.succ hz]

/-- The full extended functional is unchanged by deletion of an empty overlap
interval. This includes the zero-mass boundary of the closed parameter domain. -/
theorem closedRandomFieldParisiFunctional_erase_adjacent_eq
    (μh : Measure ℝ) {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin (k + 1) → ℝ) (qs : Fin (k + 2) → ℝ)
    (p : Fin (k + 1)) (hq : qs p.castSucc = qs p.succ) :
    closedRandomFieldParisiFunctional μh ξ
        (eraseParisiMass ms p) (eraseParisiOverlap qs p) =
      closedRandomFieldParisiFunctional μh ξ ms qs := by
  unfold closedRandomFieldParisiFunctional
  congr 1
  · congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (closedParisiX₀_erase_adjacent_eq ms qs p hq)
  · congr 1
    rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    exact parisiCorrection_erase_adjacent_eq ms qs p hq

/-- Reinsert a mass at the previous mass value. The new coordinate is zero at
the left endpoint, so the closed mass ordering is preserved. -/
def repeatParisiMass {k : ℕ} (ms : Fin k → ℝ) (p : Fin (k + 1)) :
    Fin (k + 1) → ℝ :=
  Fin.insertNth (α := fun _ => ℝ) p (mExt ms p.val) ms

@[simp] theorem erase_repeatParisiMass {k : ℕ}
    (ms : Fin k → ℝ) (p : Fin (k + 1)) :
    eraseParisiMass (repeatParisiMass ms p) p = ms := by
  funext i
  unfold eraseParisiMass repeatParisiMass
  exact Fin.insertNth_apply_succAbove _ _ _ _

theorem repeatParisiMass_mem_domain {k : ℕ} {ms : Fin k → ℝ}
    (hm : ms ∈ parisiMassDomain k) (p : Fin (k + 1)) :
    repeatParisiMass ms p ∈ parisiMassDomain (k + 1) := by
  have hb := mem_parisiMassDomain_iff.1 hm
  have hcoord : ∀ i, repeatParisiMass ms p i ∈ Icc (0 : ℝ) 1 := by
    intro i
    by_cases hi : i = p
    · subst i
      simp only [repeatParisiMass, Fin.insertNth_apply_same]
      exact ⟨mExt_nonneg hb.2.1 _, mExt_le_one hb.2.2 _⟩
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      simpa only [repeatParisiMass, Fin.insertNth_apply_succAbove] using
        (show ms j ∈ Icc (0 : ℝ) 1 from ⟨hb.2.1 j, hb.2.2 j⟩)
  refine mem_parisiMassDomain_iff.2 ⟨?_, (fun i => (hcoord i).1),
    (fun i => (hcoord i).2)⟩
  induction k with
  | zero =>
    intro a b _
    have ha : a = 0 := Fin.eq_zero a
    have hb : b = 0 := Fin.eq_zero b
    rw [ha, hb]
  | succ k =>
    refine Fin.cases ?_ (fun i => ?_) p
    · simp only [repeatParisiMass, Fin.val_zero, mExt_zero]
      exact Fin.insertNth_zero_monotone hb.1 0 (hb.2.1 0)
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [repeatParisiMass, Fin.val_succ, mExt_val_succ]
        change Monotone (Fin.insertNth (α := fun _ => ℝ) (Fin.last (k + 1))
          (ms (Fin.last k)) ms)
        exact Fin.insertNth_last_monotone hb.1 _ (le_refl _)
      · simp only [repeatParisiMass, Fin.val_succ, mExt_val_succ]
        change Monotone (Fin.insertNth (α := fun _ => ℝ) j.castSucc.succ
          (ms j.castSucc) ms)
        exact Fin.insertNth_monotone hb.1 j _ (le_refl _) (hb.1 j.castSucc_le_succ)

theorem eraseParisiMass_mem_domain {k : ℕ} {ms : Fin (k + 1) → ℝ}
    (hm : ms ∈ parisiMassDomain (k + 1)) (p : Fin (k + 1)) :
    eraseParisiMass ms p ∈ parisiMassDomain k := by
  have hb := mem_parisiMassDomain_iff.1 hm
  refine mem_parisiMassDomain_iff.2 ⟨?_, ?_, ?_⟩
  · exact hb.1.comp p.succAboveOrderEmb.monotone
  · exact fun i => hb.2.1 (p.succAbove i)
  · exact fun i => hb.2.2 (p.succAbove i)

/-- A full closed-domain minimum remains a full minimum after an empty
overlap interval is removed. Both mass and overlap competitors are lifted. -/
theorem isMinOn_closedRandomFieldParisiFunctional_erase_adjacent_eq
    (μh : Measure ℝ) {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin (k + 1) → ℝ) (qs : Fin (k + 2) → ℝ)
    (p : Fin (k + 1)) (hq : qs p.castSucc = qs p.succ)
    (hmin : IsMinOn (fun x =>
      closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain (k + 1)) (ms, qs)) :
    IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain k)
      (eraseParisiMass ms p, eraseParisiOverlap qs p) := by
  intro x hx
  change closedRandomFieldParisiFunctional μh ξ
      (eraseParisiMass ms p) (eraseParisiOverlap qs p) ≤
    closedRandomFieldParisiFunctional μh ξ x.1 x.2
  rw [closedRandomFieldParisiFunctional_erase_adjacent_eq μh ms qs p hq]
  have htest := closedRandomFieldParisiFunctional_erase_adjacent_eq μh (ξ := ξ)
    (repeatParisiMass x.1 p) (repeatParisiOverlap x.2 p) p
    (repeatParisiOverlap_adjacent_eq x.2 p)
  simp only [erase_repeatParisiMass, erase_repeatParisiOverlap] at htest
  rw [htest]
  have hcomp : (repeatParisiMass x.1 p, repeatParisiOverlap x.2 p) ∈
      parisiParameterDomain (k + 1) :=
    ⟨repeatParisiMass_mem_domain hx.1 p, repeatParisiOverlap_mem_domain hx.2 p⟩
  exact hmin hcomp

/-- Repeated-overlap deletion preserves full closed-domain minimality. -/
theorem exists_strictQ_closedRandomFieldParisiMinimum
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ms ∈ parisiMassDomain k) (hq : qs ∈ parisiOverlapDomain k)
    (hmin : IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain k) (ms, qs)) :
    ∃ (l : ℕ) (ms' : Fin l → ℝ) (qs' : Fin (l + 1) → ℝ),
      l ≤ k ∧ ms' ∈ parisiMassDomain l ∧ ParisiQAdmissible qs' ∧
      closedRandomFieldParisiFunctional μh ξ ms' qs' =
        closedRandomFieldParisiFunctional μh ξ ms qs ∧
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain l) (ms', qs') := by
  induction k with
  | zero =>
    have hs : StrictMono qs := Fin.strictMono_iff_lt_succ.2 (fun i => i.elim0)
    have hb := mem_parisiOverlapDomain_iff.1 hq
    exact ⟨0, ms, qs, le_refl _, hm, ⟨hs, hb.2.1, hb.2.2⟩, rfl, hmin⟩
  | succ k ih =>
    by_cases hs : StrictMono qs
    · have hb := mem_parisiOverlapDomain_iff.1 hq
      exact ⟨k + 1, ms, qs, le_refl _, hm, ⟨hs, hb.2.1, hb.2.2⟩, rfl, hmin⟩
    · have hn : ¬ ∀ p : Fin (k + 1), qs p.castSucc < qs p.succ :=
        fun hp => hs (Fin.strictMono_iff_lt_succ.2 hp)
      obtain ⟨p, hp⟩ := not_forall.1 hn
      have he : qs p.castSucc = qs p.succ :=
        le_antisymm (hq.2 p.castSucc_le_succ) (le_of_not_gt hp)
      obtain ⟨l, ms', qs', hl, hm', hq', hvalue, hmin'⟩ :=
        ih (eraseParisiMass ms p) (eraseParisiOverlap qs p)
          (eraseParisiMass_mem_domain hm p) (eraseParisiOverlap_mem_domain hq p)
          (isMinOn_closedRandomFieldParisiFunctional_erase_adjacent_eq
            μh ms qs p he hmin)
      exact ⟨l, ms', qs', hl.trans (Nat.le_succ k), hm', hq',
        hvalue.trans (closedRandomFieldParisiFunctional_erase_adjacent_eq μh ms qs p he),
        hmin'⟩

/-- Near-optimal full minima can be chosen with strict overlap coordinates.
The remaining normalization is removal of repeated or endpoint masses. -/
theorem exists_nearOptimal_strictQ_closedRandomFieldParisiMinimum
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ms ∈ parisiMassDomain k ∧ ParisiQAdmissible qs ∧
      closedRandomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε ∧
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) := by
  obtain ⟨k, p, hp, hnear, hmin⟩ :=
    exists_nearOptimal_closedRandomFieldParisiMinimum hμ hξ hε
  obtain ⟨l, ms, qs, _, hm, hq, hvalue, hmin'⟩ :=
    exists_strictQ_closedRandomFieldParisiMinimum μh ξ p.1 p.2 hp.1 hp.2 hmin
  exact ⟨l, ms, qs, hm, hq, hvalue.trans_lt hnear, hmin'⟩

/-- Two adjacent equal-mass Cole-Hopf levels depend only on their total
Gaussian variance. This includes mass zero and mass one. -/
theorem coleHopf_pair_eq_of_sum {A : ℝ → ℝ} {L : ℝ}
    (hA : ∀ x y, |A y - A x| ≤ L * |y - x|)
    (m : ℝ) {a b a' b' : ℝ≥0} (hsum : a + b = a' + b') :
    (fun x => coleHopf m a (coleHopf m b A) x) =
      (fun x => coleHopf m a' (coleHopf m b' A) x) := by
  have hAm : Measurable A :=
    (lipschitzWith_toNNReal_of_abs_sub_le hA).continuous.measurable
  funext x
  rw [coleHopf_coleHopf (HasLinearGrowth.of_lipschitz hA) hAm m a b x,
    coleHopf_coleHopf (HasLinearGrowth.of_lipschitz hA) hAm m a' b' x, hsum]

/-- Changing the split of variance between two equal-mass levels leaves the
whole recursion unchanged, provided the total variance is fixed. -/
theorem coleHopfIterate_eq_of_equal_mass_pair {n : ℕ} (i s : ℕ)
    (hn : n = i + (2 + s)) (ms : Fin n → ℝ) (vs ws : Fin n → ℝ≥0)
    {G : ℝ → ℝ} {L : ℝ}
    (hGm : Measurable G) (hG : ∀ x y, |G y - G x| ≤ L * |y - x|)
    (hm : ms ⟨i, by omega⟩ = ms ⟨i + 1, by omega⟩)
    (hpre : ∀ p : Fin i, vs ⟨p.val, by omega⟩ = ws ⟨p.val, by omega⟩)
    (hsuf : ∀ p : Fin s, vs ⟨i + p.val + 2, by omega⟩ =
      ws ⟨i + p.val + 2, by omega⟩)
    (hsum : vs ⟨i, by omega⟩ + vs ⟨i + 1, by omega⟩ =
      ws ⟨i, by omega⟩ + ws ⟨i + 1, by omega⟩) :
    coleHopfIterate n ms vs G = coleHopfIterate n ms ws G := by
  subst n
  rw [coleHopfIterate_split_two i s ms vs G,
    coleHopfIterate_split_two i s ms ws G]
  have hvpre : (fun p : Fin i => vs ⟨p.val, by omega⟩) =
      (fun p : Fin i => ws ⟨p.val, by omega⟩) := funext hpre
  have hvsuf : (fun p : Fin s => vs ⟨i + p.val + 2, by omega⟩) =
      (fun p : Fin s => ws ⟨i + p.val + 2, by omega⟩) := funext hsuf
  rw [hvpre, hvsuf, ← hm]
  have hAlip : ∀ x y,
      |coleHopfIterate s
          (fun p : Fin s => ms ⟨i + p.val + 2, by omega⟩)
          (fun p : Fin s => ws ⟨i + p.val + 2, by omega⟩) G y -
        coleHopfIterate s
          (fun p : Fin s => ms ⟨i + p.val + 2, by omega⟩)
          (fun p : Fin s => ws ⟨i + p.val + 2, by omega⟩) G x| ≤
        L * |y - x| :=
    abs_coleHopfIterate_sub_le s _ _ hGm hG
  have hpair := coleHopf_pair_eq_of_sum hAlip
    (ms ⟨i, by omega⟩) hsum
  exact congrArg (fun A : ℝ → ℝ =>
    coleHopfIterate i (fun p => ms ⟨p.val, by omega⟩)
      (fun p => ws ⟨p.val, by omega⟩) A) hpair

/-- A valid change of one overlap coordinate redistributes, but does not
change, the total variance of its two neighboring Gaussian levels. -/
theorem parisiVar_qUpdate_pair_sum_of_talagrand {ξ : ℝ → ℝ} {k : ℕ}
    (hξ : TalagrandXiCondition ξ) (qs : Fin (k + 1) → ℝ)
    (hq : qs ∈ parisiOverlapDomain k) (r : Fin (k + 1)) (u : ℝ)
    (hu : qExt qs r.val ≤ u ∧ u ≤ qExt qs (r.val + 2)) :
    parisiVar ξ (qUpdate qs r u) r.val +
        parisiVar ξ (qUpdate qs r u) (r.val + 1) =
      parisiVar ξ qs r.val + parisiVar ξ qs (r.val + 1) := by
  obtain ⟨hmono, hq0, hq1⟩ := mem_parisiOverlapDomain_iff.1 hq
  have hmem (n : ℕ) : qExt qs n ∈ Icc (0 : ℝ) 1 :=
    qExt_mem_Icc hmono hq0 hq1 n
  have humem : u ∈ Icc (0 : ℝ) 1 :=
    ⟨(hmem r.val).1.trans hu.1, hu.2.trans (hmem (r.val + 2)).2⟩
  have hleft : qExt qs r.val ≤ qExt qs (r.val + 1) :=
    qExt_le_succ hmono hq0 hq1 (by omega)
  have hright : qExt qs (r.val + 1) ≤ qExt qs (r.val + 2) :=
    qExt_le_succ hmono hq0 hq1 (by omega)
  have hdlu : deriv ξ (qExt qs r.val) ≤ deriv ξ u :=
    hξ.strictMonoOn_deriv.monotoneOn (hmem r.val) humem hu.1
  have hdru : deriv ξ u ≤ deriv ξ (qExt qs (r.val + 2)) :=
    hξ.strictMonoOn_deriv.monotoneOn humem (hmem (r.val + 2)) hu.2
  have hdlm : deriv ξ (qExt qs r.val) ≤ deriv ξ (qExt qs (r.val + 1)) :=
    hξ.strictMonoOn_deriv.monotoneOn (hmem r.val) (hmem (r.val + 1)) hleft
  have hdrm : deriv ξ (qExt qs (r.val + 1)) ≤
      deriv ξ (qExt qs (r.val + 2)) :=
    hξ.strictMonoOn_deriv.monotoneOn (hmem (r.val + 1))
      (hmem (r.val + 2)) hright
  rw [parisiVar_qUpdate_left, parisiVar_qUpdate_right]
  unfold parisiVar
  apply NNReal.coe_injective
  simp only [NNReal.coe_add,
    Real.coe_toNNReal _ (sub_nonneg.2 hdlu),
    Real.coe_toNNReal _ (sub_nonneg.2 hdru),
    Real.coe_toNNReal _ (sub_nonneg.2 hdlm),
    Real.coe_toNNReal _ (sub_nonneg.2 hdrm)]
  ring

/-- When the masses on both sides of a coordinate agree, moving that
coordinate within its neighboring overlap interval does not change $X_0$. -/
theorem closedParisiX₀_qUpdate_eq_of_equal_mass {ξ : ℝ → ℝ} {k : ℕ}
    (hξ : TalagrandXiCondition ξ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (hq : qs ∈ parisiOverlapDomain k)
    (r : Fin (k + 1)) (u : ℝ)
    (hm : mExt ms r.val = mExt ms (r.val + 1))
    (hu : qExt qs r.val ≤ u ∧ u ≤ qExt qs (r.val + 2)) (h : ℝ) :
    closedParisiX₀ ξ ms (qUpdate qs r u) h = closedParisiX₀ ξ ms qs h := by
  have hn : k + 2 = r.val + (2 + (k - r.val)) := by omega
  have hmass :
      (Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms))
          ⟨r.val, by omega⟩ =
        (Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms))
          ⟨r.val + 1, by omega⟩ := by
    rw [parisiAllMasses_apply, parisiAllMasses_apply]
    exact hm
  have hpre : ∀ p : Fin r.val,
      parisiAllVars ξ (qUpdate qs r u) ⟨p.val, by omega⟩ =
        parisiAllVars ξ qs ⟨p.val, by omega⟩ := by
    intro p
    change parisiVar ξ (qUpdate qs r u) p.val = parisiVar ξ qs p.val
    exact parisiVar_qUpdate_before qs r u (by omega)
  have hsuf : ∀ p : Fin (k - r.val),
      parisiAllVars ξ (qUpdate qs r u) ⟨r.val + p.val + 2, by omega⟩ =
        parisiAllVars ξ qs ⟨r.val + p.val + 2, by omega⟩ := by
    intro p
    change parisiVar ξ (qUpdate qs r u) (r.val + p.val + 2) =
      parisiVar ξ qs (r.val + p.val + 2)
    exact parisiVar_qUpdate_after qs r u (by omega)
  have hsum :
      parisiAllVars ξ (qUpdate qs r u) ⟨r.val, by omega⟩ +
          parisiAllVars ξ (qUpdate qs r u) ⟨r.val + 1, by omega⟩ =
        parisiAllVars ξ qs ⟨r.val, by omega⟩ +
          parisiAllVars ξ qs ⟨r.val + 1, by omega⟩ :=
    parisiVar_qUpdate_pair_sum_of_talagrand hξ qs hq r u hu
  unfold closedParisiX₀
  exact congrFun (coleHopfIterate_eq_of_equal_mass_pair (L := 1)
    r.val (k - r.val) hn
    (Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms))
    (parisiAllVars ξ (qUpdate qs r u)) (parisiAllVars ξ qs)
    (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal h))
    (fun x y => by simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le h x y)
    hmass hpre hsuf hsum) 0

/-- Abel summation writes the closed correction in free-coordinate form. -/
theorem closedRandomFieldParisiFunctional_eq_theta_fin_sum
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    closedRandomFieldParisiFunctional μh ξ ms qs =
      Real.log 2 + (∫ h, closedParisiX₀ ξ ms qs h ∂μh) +
        (1 / 2) * ∑ p : Fin (k + 1),
          parisiTheta ξ (qs p) * (mExt ms (p.val + 1) - mExt ms p.val) -
        (1 / 2) * parisiTheta ξ 1 := by
  have hbase := randomFieldParisiFunctional_eq_theta_fin_sum μh ξ ms qs
  unfold randomFieldParisiFunctional at hbase
  unfold closedRandomFieldParisiFunctional
  linarith

/-- A coordinate between equal masses is flat for the full closed functional. -/
theorem closedRandomFieldParisiFunctional_qUpdate_eq_of_equal_mass
    (μh : Measure ℝ) {ξ : ℝ → ℝ} {k : ℕ}
    (hξ : TalagrandXiCondition ξ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (hq : qs ∈ parisiOverlapDomain k)
    (r : Fin (k + 1)) (u : ℝ)
    (hm : mExt ms r.val = mExt ms (r.val + 1))
    (hu : qExt qs r.val ≤ u ∧ u ≤ qExt qs (r.val + 2)) :
    closedRandomFieldParisiFunctional μh ξ ms (qUpdate qs r u) =
      closedRandomFieldParisiFunctional μh ξ ms qs := by
  rw [closedRandomFieldParisiFunctional_eq_theta_fin_sum,
    closedRandomFieldParisiFunctional_eq_theta_fin_sum]
  have hX : (∫ h, closedParisiX₀ ξ ms (qUpdate qs r u) h ∂μh) =
      ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun h =>
      closedParisiX₀_qUpdate_eq_of_equal_mass hξ ms qs hq r u hm hu h)
  rw [hX]
  have hsum : (∑ p : Fin (k + 1),
      parisiTheta ξ (qUpdate qs r u p) *
        (mExt ms (p.val + 1) - mExt ms p.val)) =
      ∑ p : Fin (k + 1), parisiTheta ξ (qs p) *
        (mExt ms (p.val + 1) - mExt ms p.val) := by
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p = r
    · subst p
      simp only [qUpdate_self, hm, sub_self, mul_zero]
    · rw [qUpdate_of_ne qs u hp]
  rw [hsum]

theorem repeat_eraseParisiOverlap_eq_qUpdate_prev {k : ℕ}
    (qs : Fin (k + 2) → ℝ) (p : Fin (k + 1)) :
    repeatParisiOverlap (eraseParisiOverlap qs p) p =
      qUpdate qs p.succ (qs p.castSucc) := by
  have hp : eraseParisiOverlap qs p p = qs p.castSucc := by
    simp [eraseParisiOverlap, Fin.succAbove_of_castSucc_lt]
  unfold repeatParisiOverlap qUpdate
  rw [hp]
  exact Fin.insertNth_removeNth p.succ (qs p.castSucc) qs

/-- When two consecutive extended masses agree, the intervening overlap may
be moved to its predecessor and then deleted without changing the value. -/
theorem closedRandomFieldParisiFunctional_repeat_erase_eq_of_equal_mass
    (μh : Measure ℝ) {ξ : ℝ → ℝ} {k : ℕ}
    (hξ : TalagrandXiCondition ξ) (ms : Fin (k + 1) → ℝ)
    (qs : Fin (k + 2) → ℝ) (hq : qs ∈ parisiOverlapDomain (k + 1))
    (p : Fin (k + 1))
    (hm : mExt ms (p.val + 1) = mExt ms (p.val + 2)) :
    closedRandomFieldParisiFunctional μh ξ ms
        (repeatParisiOverlap (eraseParisiOverlap qs p) p) =
      closedRandomFieldParisiFunctional μh ξ ms qs := by
  obtain ⟨hmono, hq0, hq1⟩ := mem_parisiOverlapDomain_iff.1 hq
  have hp1 : qExt qs (p.val + 1) = qs p.castSucc := by
    rw [qExt_succ_of_lt qs (by omega)]
    rfl
  have hu : qExt qs p.succ.val ≤ qs p.castSucc ∧
      qs p.castSucc ≤ qExt qs (p.succ.val + 2) := by
    constructor
    · simpa only [Fin.val_succ, hp1] using (le_refl (qs p.castSucc))
    · calc
        qs p.castSucc = qExt qs (p.val + 1) := hp1.symm
        _ ≤ qExt qs (p.val + 2) := qExt_le_succ hmono hq0 hq1 (by omega)
        _ ≤ qExt qs (p.val + 3) := qExt_le_succ hmono hq0 hq1 (by omega)
        _ = qExt qs (p.succ.val + 2) := by simp
  rw [repeat_eraseParisiOverlap_eq_qUpdate_prev]
  exact closedRandomFieldParisiFunctional_qUpdate_eq_of_equal_mass
    μh hξ ms qs hq p.succ (qs p.castSucc) (by simpa using hm) hu

/-- Moving the first overlap to the second produces a closed-domain list. -/
theorem qUpdate_first_to_second_mem_domain {k : ℕ}
    {qs : Fin (k + 2) → ℝ} (hq : qs ∈ parisiOverlapDomain (k + 1)) :
    qUpdate qs 0 (qs 1) ∈ parisiOverlapDomain (k + 1) := by
  have hc : ∀ i, qUpdate qs 0 (qs 1) i ∈ Icc (0 : ℝ) 1 := by
    intro i
    by_cases hi : i = 0
    · subst i
      simpa only [qUpdate_self] using (mem_parisiOverlapCube_iff.1 hq.1 (1 : Fin (k + 2)))
    · rw [qUpdate_of_ne qs _ hi]
      exact mem_parisiOverlapCube_iff.1 hq.1 i
  refine ⟨mem_parisiOverlapCube_iff.2 hc, Fin.monotone_iff_le_succ.2 ?_⟩
  intro i
  by_cases hi : i = 0
  · subst i
    simp [qUpdate]
  · have hcast : i.castSucc ≠ (0 : Fin (k + 2)) := by
      intro he
      apply hi
      exact Fin.ext (by simpa using congrArg Fin.val he)
    have hsucc : i.succ ≠ (0 : Fin (k + 2)) := Fin.succ_ne_zero _
    rw [qUpdate_of_ne qs _ hcast, qUpdate_of_ne qs _ hsucc]
    exact hq.2 i.castSucc_le_succ

theorem closedRandomFieldParisiFunctional_first_zero_mass_eq
    (μh : Measure ℝ) {ξ : ℝ → ℝ} {k : ℕ}
    (hξ : TalagrandXiCondition ξ) (ms : Fin (k + 1) → ℝ)
    (qs : Fin (k + 2) → ℝ) (hq : qs ∈ parisiOverlapDomain (k + 1))
    (hm0 : ms 0 = 0) :
    closedRandomFieldParisiFunctional μh ξ ms (qUpdate qs 0 (qs 1)) =
      closedRandomFieldParisiFunctional μh ξ ms qs := by
  have hq1 : qExt qs 2 = qs 1 := by
    rw [qExt_succ_of_lt qs (by omega : 1 < k + 2)]
    rfl
  have hu : qExt qs 0 ≤ qs 1 ∧ qs 1 ≤ qExt qs 2 := by
    rw [qExt_zero, hq1]
    exact ⟨(mem_parisiOverlapCube_iff.1 hq.1 1).1, le_refl _⟩
  exact closedRandomFieldParisiFunctional_qUpdate_eq_of_equal_mass μh hξ ms qs hq
    0 (qs 1) (by simp [mExt_one, hm0]) hu

/-- A repeated interior or last mass lowers the level count while preserving
the closed-domain minimum and its value. -/
theorem reduce_closedRandomFieldParisiMinimum_of_equal_mass
    (μh : Measure ℝ) {ξ : ℝ → ℝ} {k : ℕ}
    (hξ : TalagrandXiCondition ξ) (ms : Fin (k + 1) → ℝ)
    (qs : Fin (k + 2) → ℝ)
    (hm : ms ∈ parisiMassDomain (k + 1))
    (hq : qs ∈ parisiOverlapDomain (k + 1))
    (hmin : IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain (k + 1)) (ms, qs))
    (p : Fin (k + 1))
    (he : mExt ms (p.val + 1) = mExt ms (p.val + 2)) :
    ∃ (ms' : Fin k → ℝ) (qs' : Fin (k + 1) → ℝ),
      ms' ∈ parisiMassDomain k ∧ qs' ∈ parisiOverlapDomain k ∧
      closedRandomFieldParisiFunctional μh ξ ms' qs' =
        closedRandomFieldParisiFunctional μh ξ ms qs ∧
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms', qs') := by
  let qu := repeatParisiOverlap (eraseParisiOverlap qs p) p
  have hqu : qu ∈ parisiOverlapDomain (k + 1) :=
    repeatParisiOverlap_mem_domain (eraseParisiOverlap_mem_domain hq p) p
  have hflat : closedRandomFieldParisiFunctional μh ξ ms qu =
      closedRandomFieldParisiFunctional μh ξ ms qs :=
    closedRandomFieldParisiFunctional_repeat_erase_eq_of_equal_mass
      μh hξ ms qs hq p he
  have hrepeat : qu p.castSucc = qu p.succ :=
    repeatParisiOverlap_adjacent_eq _ p
  have hminqu : IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain (k + 1)) (ms, qu) := by
    intro x hx
    change closedRandomFieldParisiFunctional μh ξ ms qu ≤
      closedRandomFieldParisiFunctional μh ξ x.1 x.2
    rw [hflat]
    exact hmin hx
  refine ⟨eraseParisiMass ms p, eraseParisiOverlap qu p,
    eraseParisiMass_mem_domain hm p, eraseParisiOverlap_mem_domain hqu p, ?_, ?_⟩
  · exact (closedRandomFieldParisiFunctional_erase_adjacent_eq μh ms qu p hrepeat).trans
      hflat
  · exact isMinOn_closedRandomFieldParisiFunctional_erase_adjacent_eq
      μh ms qu p hrepeat hminqu

/-- A zero first mass is merged with the root Gaussian expectation and then
deleted, preserving the closed-domain minimum. -/
theorem reduce_closedRandomFieldParisiMinimum_of_first_zero_mass
    (μh : Measure ℝ) {ξ : ℝ → ℝ} {k : ℕ}
    (hξ : TalagrandXiCondition ξ) (ms : Fin (k + 1) → ℝ)
    (qs : Fin (k + 2) → ℝ)
    (hm : ms ∈ parisiMassDomain (k + 1))
    (hq : qs ∈ parisiOverlapDomain (k + 1))
    (hmin : IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain (k + 1)) (ms, qs)) (hm0 : ms 0 = 0) :
    ∃ (ms' : Fin k → ℝ) (qs' : Fin (k + 1) → ℝ),
      ms' ∈ parisiMassDomain k ∧ qs' ∈ parisiOverlapDomain k ∧
      closedRandomFieldParisiFunctional μh ξ ms' qs' =
        closedRandomFieldParisiFunctional μh ξ ms qs ∧
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms', qs') := by
  let qu := qUpdate qs 0 (qs 1)
  have hqu : qu ∈ parisiOverlapDomain (k + 1) :=
    qUpdate_first_to_second_mem_domain hq
  have hflat : closedRandomFieldParisiFunctional μh ξ ms qu =
      closedRandomFieldParisiFunctional μh ξ ms qs :=
    closedRandomFieldParisiFunctional_first_zero_mass_eq μh hξ ms qs hq hm0
  have hrepeat : qu (0 : Fin (k + 1)).castSucc = qu (0 : Fin (k + 1)).succ := by
    simp [qu, qUpdate]
  have hminqu : IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain (k + 1)) (ms, qu) := by
    intro x hx
    change closedRandomFieldParisiFunctional μh ξ ms qu ≤
      closedRandomFieldParisiFunctional μh ξ x.1 x.2
    rw [hflat]
    exact hmin hx
  refine ⟨eraseParisiMass ms 0, eraseParisiOverlap qu 0,
    eraseParisiMass_mem_domain hm 0, eraseParisiOverlap_mem_domain hqu 0, ?_, ?_⟩
  · exact (closedRandomFieldParisiFunctional_erase_adjacent_eq μh ms qu 0 hrepeat).trans
      hflat
  · exact isMinOn_closedRandomFieldParisiFunctional_erase_adjacent_eq
      μh ms qu 0 hrepeat hminqu

/-- Repeated or endpoint masses can be deleted while retaining a minimum over
the entire closed parameter domain. -/
theorem exists_strictM_closedRandomFieldParisiMinimum
    (μh : Measure ℝ) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ms ∈ parisiMassDomain k) (hq : qs ∈ parisiOverlapDomain k)
    (hmin : IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain k) (ms, qs)) :
    ∃ (l : ℕ) (ms' : Fin l → ℝ) (qs' : Fin (l + 1) → ℝ),
      l ≤ k ∧ ParisiMAdmissible ms' ∧ qs' ∈ parisiOverlapDomain l ∧
      closedRandomFieldParisiFunctional μh ξ ms' qs' =
        closedRandomFieldParisiFunctional μh ξ ms qs ∧
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain l) (ms', qs') := by
  induction k with
  | zero =>
    have hs : StrictMono ms := by
      intro i j _
      exact i.elim0
    exact ⟨0, ms, qs, le_refl _,
      ⟨hs, (fun i => i.elim0), (fun i => i.elim0)⟩, hq, rfl, hmin⟩
  | succ k ih =>
    have hb := mem_parisiMassDomain_iff.1 hm
    by_cases hzero : ms 0 = 0
    · obtain ⟨ms', qs', hm', hq', heq, hmin'⟩ :=
        reduce_closedRandomFieldParisiMinimum_of_first_zero_mass
          μh hξ ms qs hm hq hmin hzero
      obtain ⟨l, ms'', qs'', hl, hstrict, hq'', heq', hmin''⟩ :=
        ih ms' qs' hm' hq' hmin'
      exact ⟨l, ms'', qs'', hl.trans (Nat.le_succ k), hstrict, hq'',
        heq'.trans heq, hmin''⟩
    by_cases hstrict : StrictMono ms
    · by_cases hlast : ms (Fin.last k) = 1
      · have he : mExt ms ((Fin.last k).val + 1) =
            mExt ms ((Fin.last k).val + 2) := by
          have hleft : mExt ms ((Fin.last k).val + 1) = ms (Fin.last k) :=
            mExt_val_succ ms (Fin.last k)
          simp only [Fin.val_last] at hleft ⊢
          rw [hleft, mExt_eq_one_of_le (ms := ms) (by omega)]
          exact hlast
        obtain ⟨ms', qs', hm', hq', heq, hmin'⟩ :=
          reduce_closedRandomFieldParisiMinimum_of_equal_mass
            μh hξ ms qs hm hq hmin (Fin.last k) he
        obtain ⟨l, ms'', qs'', hl, hstrict', hq'', heq', hmin''⟩ :=
          ih ms' qs' hm' hq' hmin'
        exact ⟨l, ms'', qs'', hl.trans (Nat.le_succ k), hstrict', hq'',
          heq'.trans heq, hmin''⟩
      · have hpos : ∀ i, 0 < ms i := by
          intro i
          exact lt_of_le_of_ne (hb.2.1 i) (by
            intro hi
            apply hzero
            have hle := hstrict.monotone (Fin.zero_le i)
            rw [← hi] at hle
            exact le_antisymm hle (hb.2.1 0))
        have hlt : ∀ i, ms i < 1 := by
          intro i
          exact lt_of_le_of_ne (hb.2.2 i) (by
            intro hi
            apply hlast
            have hle := hstrict.monotone (Fin.le_last i)
            rw [hi] at hle
            exact le_antisymm (hb.2.2 (Fin.last k)) hle)
        exact ⟨k + 1, ms, qs, le_refl _, ⟨hstrict, hpos, hlt⟩, hq, rfl, hmin⟩
    · have hn : ¬ ∀ p : Fin k, ms p.castSucc < ms p.succ :=
        fun hp => hstrict (Fin.strictMono_iff_lt_succ.2 hp)
      obtain ⟨p, hp⟩ := not_forall.1 hn
      have heqMass : ms p.castSucc = ms p.succ :=
        le_antisymm (hb.1 p.castSucc_le_succ) (le_of_not_gt hp)
      have he : mExt ms (p.castSucc.val + 1) =
          mExt ms (p.castSucc.val + 2) := by
        have hleft : mExt ms (p.castSucc.val + 1) = ms p.castSucc :=
          mExt_val_succ ms p.castSucc
        have hright : mExt ms (p.castSucc.val + 2) = ms p.succ := by
          simpa only [Fin.val_castSucc, Fin.val_succ] using mExt_val_succ ms p.succ
        rw [hleft, hright]
        exact heqMass
      obtain ⟨ms', qs', hm', hq', heq, hmin'⟩ :=
        reduce_closedRandomFieldParisiMinimum_of_equal_mass
          μh hξ ms qs hm hq hmin p.castSucc he
      obtain ⟨l, ms'', qs'', hl, hstrict', hq'', heq', hmin''⟩ :=
        ih ms' qs' hm' hq' hmin'
      exact ⟨l, ms'', qs'', hl.trans (Nat.le_succ k), hstrict', hq'',
        heq'.trans heq, hmin''⟩

/-- Deleting repeated overlaps after mass normalization keeps the strict mass
condition and full fixed-level minimality. -/
theorem exists_strictQ_closedRandomFieldParisiMinimum_of_strictM
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : qs ∈ parisiOverlapDomain k)
    (hmin : IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain k) (ms, qs)) :
    ∃ (l : ℕ) (ms' : Fin l → ℝ) (qs' : Fin (l + 1) → ℝ),
      l ≤ k ∧ ParisiMAdmissible ms' ∧ ParisiQAdmissible qs' ∧
      closedRandomFieldParisiFunctional μh ξ ms' qs' =
        closedRandomFieldParisiFunctional μh ξ ms qs ∧
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain l) (ms', qs') := by
  induction k with
  | zero =>
    have hs : StrictMono qs := Fin.strictMono_iff_lt_succ.2 (fun i => i.elim0)
    have hb := mem_parisiOverlapDomain_iff.1 hq
    exact ⟨0, ms, qs, le_refl _, hm, ⟨hs, hb.2.1, hb.2.2⟩, rfl, hmin⟩
  | succ k ih =>
    by_cases hs : StrictMono qs
    · have hb := mem_parisiOverlapDomain_iff.1 hq
      exact ⟨k + 1, ms, qs, le_refl _, hm, ⟨hs, hb.2.1, hb.2.2⟩,
        rfl, hmin⟩
    · have hn : ¬ ∀ p : Fin (k + 1), qs p.castSucc < qs p.succ :=
        fun hp => hs (Fin.strictMono_iff_lt_succ.2 hp)
      obtain ⟨p, hp⟩ := not_forall.1 hn
      have he : qs p.castSucc = qs p.succ :=
        le_antisymm (hq.2 p.castSucc_le_succ) (le_of_not_gt hp)
      obtain ⟨l, ms', qs', hl, hm', hq', hvalue, hmin'⟩ :=
        ih (eraseParisiMass ms p) (eraseParisiOverlap qs p)
          (hm.eraseParisiMass p) (eraseParisiOverlap_mem_domain hq p)
          (isMinOn_closedRandomFieldParisiFunctional_erase_adjacent_eq
            μh ms qs p he hmin)
      exact ⟨l, ms', qs', hl.trans (Nat.le_succ k), hm', hq',
        hvalue.trans (closedRandomFieldParisiFunctional_erase_adjacent_eq
          μh ms qs p he), hmin'⟩

/-- Full closed-domain minimality specializes to the existing overlap
minimizer API on strict parameter lists. -/
theorem isRandomFieldParisiQMinimizer_of_closedMinimum
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hmin : IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain k) (ms, qs)) :
    IsRandomFieldParisiQMinimizer μh ξ ms qs := by
  refine ⟨hq, ?_⟩
  intro qs' hq'
  have hms : ms ∈ parisiMassDomain k :=
    mem_parisiMassDomain_iff.2
      ⟨hm.1.monotone, (fun i => (hm.2.1 i).le), (fun i => (hm.2.2 i).le)⟩
  have hqs' : qs' ∈ parisiOverlapDomain k :=
    mem_parisiOverlapDomain_iff.2 ⟨hq'.1.monotone, hq'.2.1, hq'.2.2⟩
  rw [← closedRandomFieldParisiFunctional_eq μh ξ ms qs hm,
    ← closedRandomFieldParisiFunctional_eq μh ξ ms qs' hm]
  exact hmin (a := (ms, qs')) ⟨hms, hqs'⟩

/-- Talagrand's MIN parameters: a near-global optimum which is an exact
minimum over all closed mass and overlap competitors at its level count. -/
theorem exists_randomFieldParisiMIN
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms ∧ ParisiQAdmissible qs ∧
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε ∧
      IsRandomFieldParisiQMinimizer μh ξ ms qs ∧
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) := by
  obtain ⟨k, p, hp, hnear, hmin⟩ :=
    exists_nearOptimal_closedRandomFieldParisiMinimum hμ hξ hε
  obtain ⟨l, ms, qs, _, hm, hq, heq, hmin'⟩ :=
    exists_strictM_closedRandomFieldParisiMinimum μh hξ p.1 p.2 hp.1 hp.2 hmin
  obtain ⟨j, ms', qs', _, hm', hq', heq', hmin''⟩ :=
    exists_strictQ_closedRandomFieldParisiMinimum_of_strictM
      μh ξ ms qs hm hq hmin'
  refine ⟨j, ms', qs', hm', hq', ?_,
    isRandomFieldParisiQMinimizer_of_closedMinimum μh ξ ms' qs' hm' hq' hmin'',
    hmin''⟩
  rw [← closedRandomFieldParisiFunctional_eq μh ξ ms' qs' hm']
  exact (heq'.trans heq).trans_lt hnear

end SpinGlass
