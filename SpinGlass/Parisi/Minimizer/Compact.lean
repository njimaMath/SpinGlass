import SpinGlass.Parisi.Variational.ParisiMin
import SpinGlass.Parisi.Variational.ParisiMassContinuity
import SpinGlass.Parisi.Variational.ParisiLevelReduction

/-!
# Compact

Closed parameter domains, continuity, and fixed-level minimum.
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


end SpinGlass
