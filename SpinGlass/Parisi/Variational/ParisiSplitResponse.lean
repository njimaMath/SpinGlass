import SpinGlass.Parisi.Variational.ParisiRootMVariation
import SpinGlass.Parisi.Variational.ParisiVariancePropagation

/-!
# Identifying inserted functional derivatives with the variance response

The root interval uses the complete recursion after the first free overlap.
The identities here distinguish that input from a suffix which also removes
the first positive-mass layer. They connect the actual split arrays to the
operator notation of (14.238)-(14.239).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- The actual recursion after the root Gaussian, including its first layer. -/
noncomputable def parisiRootSuffix (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) : ℝ → ℝ :=
  coleHopfIterate (k + 1) (parisiLevelMasses ms) (parisiLevelVars ξ qs)
    (parisiLogCoshTerminal 0)

/-- All Gaussian intervals strictly after the split root retain their variance. -/
theorem parisiVar_splitParisiRootOverlap_after (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (u : ℝ) (n : ℕ) :
    parisiVar ξ (splitParisiRootOverlap qs u) (n + 2) = parisiVar ξ qs (n + 1) := by
  unfold parisiVar
  rw [show n + 2 + 1 = (n + 1) + 2 by omega,
    qExt_splitParisiRootOverlap_succ, qExt_splitParisiRootOverlap_succ]

/-- The concrete closed root recursion is exactly the initial two-layer split.
The formula is valid even for nonadmissible parameters and clamped variances. -/
theorem closedParisiX₀_split_root_eq (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (m u h : ℝ) :
    closedParisiX₀ ξ (splitParisiRootMass ms m) (splitParisiRootOverlap qs u) h =
      coleHopf 0 (deriv ξ u - deriv ξ 0).toNNReal
        (coleHopf m (deriv ξ (qs 0) - deriv ξ u).toNNReal (parisiRootSuffix ξ ms qs)) h := by
  have hmass : parisiLevelMasses (splitParisiRootMass ms m) =
      Fin.cons m (parisiLevelMasses ms) := by
    exact (Fin.cons_snoc_eq_snoc_cons m ms 1).symm
  have hvars : parisiAllVars ξ (splitParisiRootOverlap qs u) =
      Fin.cons (deriv ξ u - deriv ξ 0).toNNReal
        (Fin.cons (deriv ξ (qs 0) - deriv ξ u).toNNReal (parisiLevelVars ξ qs)) := by
    funext p
    refine Fin.cases ?_ (fun t => ?_) p
    · simp [parisiAllVars, parisiVar, qExt_succ_of_lt, splitParisiRootOverlap]
    · refine Fin.cases ?_ (fun r => ?_) t
      · simp [parisiAllVars, parisiVar, qExt_succ_of_lt, splitParisiRootOverlap]
      · simp only [Fin.cons_succ, parisiAllVars, parisiLevelVars, Fin.val_succ]
        exact parisiVar_splitParisiRootOverlap_after ξ qs u r.val
  rw [closedParisiX₀_translate, hmass, hvars, coleHopfIterate_succ, coleHopfIterate_succ]
  rfl

/-- Fourth-order regularity and bounded derivatives for the actual post-root
recursion, with no mass or variance nondegeneracy assumptions. -/
theorem parisiRootSuffix_spatial_regular_four (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    ContDiff ℝ 4 (parisiRootSuffix ξ ms qs) ∧
      ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv j (parisiRootSuffix ξ ms qs) x| ≤ C :=
  coleHopfIterate_spatial_regular_four (parisiLevelMasses ms) (parisiLevelVars ξ qs)
    (contDiff_parisiLogCoshTerminal 0 4) (exists_bound_iteratedDeriv_parisiLogCoshTerminal_four 0)

/-- The actual post-root recursion retains the terminal Lipschitz bound. -/
theorem abs_parisiRootSuffix_sub_le (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (x y : ℝ) :
    |parisiRootSuffix ξ ms qs y - parisiRootSuffix ξ ms qs x| ≤ |y - x| := by
  simpa only [parisiRootSuffix, one_mul] using abs_coleHopfIterate_sub_le (L := 1) (k + 1)
    (parisiLevelMasses ms) (parisiLevelVars ξ qs)
    (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0))
    (fun x y => by simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0 x y) x y

/-- The suffix following the inserted root mass is the complete original
post-root recursion, independently of the inserted mass and overlap. -/
theorem parisiQSuffix_split_root_eq (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (m u : ℝ) :
    parisiQSuffix ξ 0 (splitParisiRootMass ms m) (splitParisiRootOverlap qs u) 0 =
      parisiRootSuffix ξ ms qs := by
  have hm : parisiQSuffixMasses (splitParisiRootMass ms m) 0 =
      parisiLevelMasses ms := by
    funext p
    simp only [parisiQSuffixMasses, Fin.val_zero, zero_add, mExt_succ_tail,
      splitParisiRootMass, Fin.tail_cons]
    exact (parisiLevelMasses_apply ms p).symm
  have hv : parisiQSuffixVars ξ (splitParisiRootOverlap qs u) 0 =
      parisiLevelVars ξ qs := by
    funext p
    simp only [parisiQSuffixVars, Fin.val_zero, zero_add, parisiLevelVars]
    exact parisiVar_splitParisiRootOverlap_after ξ qs u p.val
  simp only [parisiQSuffix, Fin.val_zero, Nat.sub_zero, hm, hv, parisiRootSuffix]

/-- The concrete root mass moment equals the field average of the local
zero-mass response in (14.238). All variances retain their actual clamps. -/
theorem randomFieldParisiMassMoment_split_root_eq
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (u : ℝ) :
    randomFieldParisiMassMoment μh ξ (splitParisiRootMass ms 0)
        (splitParisiRootOverlap qs u) 0 0 =
      ∫ h, coleHopfSplitMassResponse 0 (deriv ξ (qs 0) - deriv ξ 0)
        (parisiRootSuffix ξ ms qs) h (deriv ξ (qs 0) - deriv ξ u) ∂μh := by
  have hLip := abs_parisiRootSuffix_sub_le ξ ms qs
  have hAm := (parisiRootSuffix_spatial_regular_four ξ ms qs).1.continuous.measurable
  have hpm : parisiMassPrefixMasses (splitParisiRootMass ms 0) 0 =
      (Fin.elim0 : Fin 0 → ℝ) := funext fun p => Fin.elim0 p
  have hpv : parisiMassPrefixVars ξ (splitParisiRootOverlap qs u) 0 =
      (Fin.elim0 : Fin 0 → ℝ≥0) := funext fun p => Fin.elim0 p
  have hv₀ : parisiVar ξ (splitParisiRootOverlap qs u) 0 =
      (deriv ξ u - deriv ξ 0).toNNReal := by
    simp [parisiVar, qExt_succ_of_lt, splitParisiRootOverlap]
  have hv₁ : parisiVar ξ (splitParisiRootOverlap qs u) 1 =
      (deriv ξ (qs 0) - deriv ξ u).toNNReal := by
    simp [parisiVar, qExt_succ_of_lt, splitParisiRootOverlap]
  unfold randomFieldParisiMassMoment
  apply integral_congr_ae (.of_forall fun h => ?_)
  rw [coleHopfSplitMassResponse_zero_mass_eq hAm hLip]
  have hv : deriv ξ (qs 0) - deriv ξ 0 - (deriv ξ (qs 0) - deriv ξ u) =
      deriv ξ u - deriv ξ 0 := by ring
  rw [hv]
  change (∫ z, coleHopfIterateMassDeriv
      (parisiMassPrefixMasses (splitParisiRootMass ms 0) 0)
      (parisiMassPrefixVars ξ (splitParisiRootOverlap qs u) 0)
      (parisiVar ξ (splitParisiRootOverlap qs u) 1)
      (parisiQSuffix ξ 0 (splitParisiRootMass ms 0) (splitParisiRootOverlap qs u) 0)
      0 (h + z) ∂gaussianReal 0 (parisiVar ξ (splitParisiRootOverlap qs u) 0)) = _
  rw [hpm, hpv, parisiQSuffix_split_root_eq, hv₀, hv₁]
  exact integral_congr_ae (.of_forall fun z =>
    coleHopfIterateMassDeriv_zero hAm hLip _ ⟨le_rfl, zero_le_one⟩ (h + z))

/-- Talagrand's U for the initial interval, normalized as in (14.238)-(14.239). -/
noncomputable def parisiRootU (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (v : ℝ) : ℝ :=
  2 * ∫ h, coleHopfSplitMassResponse 0 (deriv ξ (qs 0) - deriv ξ 0)
    (parisiRootSuffix ξ ms qs) h v ∂μh

/-- The first two spatial moments governing U' and U'' at the root. -/
noncomputable def parisiRootUSpatialMoment (j : ℕ) (μh : Measure ℝ)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (v : ℝ) : ℝ :=
  ∫ h, coleHopfSplitSpatialMoment j 0 (deriv ξ (qs 0) - deriv ξ 0)
    (parisiRootSuffix ξ ms qs) h v ∂μh

/-- The actual root split-functional derivative has precisely the correction
and U normalization of (14.239), including its zero matching mass. -/
theorem splitParisiRootMassDeriv_eq_U
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (u : ℝ) :
    splitParisiRootMassDeriv μh ξ ms qs u 0 =
      (1 / 2) * (parisiRootU μh ξ ms qs (deriv ξ (qs 0) - deriv ξ u) -
        (parisiTheta ξ (qs 0) - parisiTheta ξ u)) := by
  rw [splitParisiRootMassDeriv, randomFieldParisiMassMoment_split_root_eq, parisiRootU]
  ring

/-- The response is zero when the inserted root interval has zero variance. -/
theorem parisiRootU_zero (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) : parisiRootU μh ξ ms qs 0 = 0 := by
  simp only [parisiRootU, coleHopfSplitMassResponse_zero, integral_zero, mul_zero]

/-- U' is the concrete first spatial moment on the admissible variance
interval, with one-sided derivatives at either endpoint of (14.240). -/
theorem hasDerivWithinAt_parisiRootU
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (ha : 0 < deriv ξ (qs 0) - deriv ξ 0) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) :
    HasDerivWithinAt (parisiRootU μh ξ ms qs)
      (parisiRootUSpatialMoment 1 μh ξ ms qs v)
      (Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) v := by
  obtain ⟨hA, hb⟩ := parisiRootSuffix_spatial_regular_four ξ ms qs
  have hd := hasDerivWithinAt_integral_coleHopfSplitMassResponse_comp
    (μ := μh) measurable_id hA hb (abs_parisiRootSuffix_sub_le ξ ms qs)
    (m := 0) ⟨le_rfl, zero_le_one⟩ ha hv
  simp only [id_eq] at hd
  unfold parisiRootU parisiRootUSpatialMoment
  convert hd.const_mul 2 using 1 <;> first | rfl | ring

/-- U'' is minus the concrete second spatial moment, so it has the
dissipation sign in (14.240), including both variance endpoints. -/
theorem hasDerivWithinAt_parisiRootUSpatialMoment_one
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (ha : 0 < deriv ξ (qs 0) - deriv ξ 0) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) :
    HasDerivWithinAt (parisiRootUSpatialMoment 1 μh ξ ms qs)
      (-parisiRootUSpatialMoment 2 μh ξ ms qs v)
      (Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) v := by
  obtain ⟨hA, hb⟩ := parisiRootSuffix_spatial_regular_four ξ ms qs
  unfold parisiRootUSpatialMoment
  simpa only [id_eq] using
    hasDerivWithinAt_integral_coleHopfSplitSpatialMoment_comp
      (μ := μh) measurable_id hA hb (abs_parisiRootSuffix_sub_le ξ ms qs)
      (m := 0) ⟨le_rfl, zero_le_one⟩ ha hv

/-- Each actual root spatial moment is nonnegative. -/
theorem parisiRootUSpatialMoment_nonneg (j : ℕ) (μh : Measure ℝ)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (v : ℝ) :
    0 ≤ parisiRootUSpatialMoment j μh ξ ms qs v :=
  integral_nonneg fun h => coleHopfSplitSpatialMoment_nonneg j 0 _ _ h v

/-- The initial squared moment is the old first q-moment, using the actual
spatial derivative of the complete post-root recursion. -/
theorem parisiQMoment_first_eq_root_spatial_moment
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (h : ℝ) :
    parisiQMoment ξ h ms qs 0 =
      coleHopfSplitSpatialMoment 1 0 (deriv ξ (qs 0) - deriv ξ 0)
        (parisiRootSuffix ξ ms qs) h 0 := by
  have hpos : ∀ p, 0 < parisiLevelMasses ms p := by
    intro p
    rw [parisiLevelMasses_apply]
    exact hm.mExt_pos (by omega)
  have hd := (coleHopfIterate_logCosh_regular
    (parisiLevelMasses ms) (parisiLevelVars ξ qs) 0 hpos).1
  have htrans : ∀ z,
      coleHopfIterateDeriv (k + 1) (parisiLevelMasses ms) (parisiLevelVars ξ qs)
        (parisiLogCoshTerminal h) (parisiLogCoshTerminalDeriv h) z =
      deriv (parisiRootSuffix ξ ms qs) (h + z) := by
    intro z
    have hG : parisiLogCoshTerminal h = fun y => parisiLogCoshTerminal 0 (h + y) := by
      funext y
      simp only [parisiLogCoshTerminal, zero_add]
    have hG' : parisiLogCoshTerminalDeriv h =
        fun y => parisiLogCoshTerminalDeriv 0 (h + y) := by
      funext y
      simp only [parisiLogCoshTerminalDeriv, zero_add]
    rw [hG, hG', coleHopfIterateDeriv_translate]
    exact (hd (h + z)).deriv.symm
  have hzero : coleHopf 0 (0 : ℝ≥0) (parisiRootSuffix ξ ms qs) =
      parisiRootSuffix ξ ms qs := funext fun x => coleHopf_zero_var 0 _ x
  have hQzero : ∀ (v : ℝ≥0) (A : ℝ → ℝ) (x z : ℝ), coleHopfQ 0 v A x z = 1 := by
    intro v A x z
    simp only [coleHopfQ, zero_mul, Real.exp_zero]
  unfold parisiQMoment coleHopfSplitSpatialMoment
  simp only [Fin.val_zero, zero_add, ite_true, mExt_zero, qExt_zero,
    Real.toNNReal_zero, hzero, iteratedDeriv_one, sub_zero,
    coleHopfSplitMoment, hQzero, mul_one]
  apply integral_congr_ae (.of_forall fun z => ?_)
  rw [parisiQFirstInner_eq_coleHopfIterateDeriv, htrans]

/-- The root moment in U'(0) is exactly the random-field stationary q-moment,
with the field integral identified rather than assumed. -/
theorem parisiRootUSpatialMoment_one_zero_eq_randomFieldParisiQMoment
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) :
    parisiRootUSpatialMoment 1 μh ξ ms qs 0 = randomFieldParisiQMoment μh ξ ms qs 0 := by
  unfold parisiRootUSpatialMoment randomFieldParisiQMoment
  exact integral_congr_ae (.of_forall fun h =>
    (parisiQMoment_first_eq_root_spatial_moment ξ ms qs hm h).symm)

/-- For MIN's q-minimizer, the book identity U'(0)=q₁ follows from the
nondegenerate field law and Proposition 14.7.5, with a one-sided derivative. -/
theorem hasDerivWithinAt_parisiRootU_zero_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    HasDerivWithinAt (parisiRootU μh ξ ms qs) (qs 0)
      (Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) 0 := by
  obtain ⟨_, hstat⟩ :=
    randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin ms qs hm hξ hμ hmin
  have hqpos := randomFieldParisiQ_first_pos_of_isMin ms qs hμ.integrable_id hm hξ hμ hmin
  have ha : 0 < deriv ξ (qs 0) - deriv ξ 0 := sub_pos.2
    (hξ.strictMonoOn_deriv ⟨le_rfl, zero_le_one⟩ (hmin.1.mem_Icc 0) hqpos)
  have hd := hasDerivWithinAt_parisiRootU (μh := μh) ξ ms qs ha
    (v := 0) ⟨le_rfl, ha.le⟩
  rw [parisiRootUSpatialMoment_one_zero_eq_randomFieldParisiQMoment μh ξ ms qs hm,
    ← hstat 0] at hd
  exact hd

/-- The derivative form of U'(0)=q₁ on its genuine admissible variance domain. -/
theorem derivWithin_parisiRootU_zero_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    derivWithin (parisiRootU μh ξ ms qs)
      (Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) 0 = qs 0 := by
  have hqpos := randomFieldParisiQ_first_pos_of_isMin ms qs hμ.integrable_id hm hξ hμ hmin
  have ha : 0 < deriv ξ (qs 0) - deriv ξ 0 := sub_pos.2
    (hξ.strictMonoOn_deriv ⟨le_rfl, zero_le_one⟩ (hmin.1.mem_Icc 0) hqpos)
  exact (hasDerivWithinAt_parisiRootU_zero_of_isMin ms qs hm hξ hμ hmin).derivWithin
    (uniqueDiffOn_Icc ha 0 ⟨le_rfl, ha.le⟩)

/-- The one-sided mass derivative of the actual root split functional in
(14.239), with no derivative or moment identity supplied by the caller. -/
theorem hasDerivWithinAt_closedRandomFieldParisiFunctional_split_root_mass_zero_eq_U
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (u : ℝ) :
    HasDerivWithinAt
      (fun b => closedRandomFieldParisiFunctional μh ξ
        (splitParisiRootMass ms b) (splitParisiRootOverlap qs u))
      ((1 / 2) * (parisiRootU μh ξ ms qs (deriv ξ (qs 0) - deriv ξ u) -
        (parisiTheta ξ (qs 0) - parisiTheta ξ u))) (Icc (0 : ℝ) 1) 0 := by
  rw [← splitParisiRootMassDeriv_eq_U]
  exact hasDerivWithinAt_closedRandomFieldParisiFunctional_split_root_mass hμ ξ ms qs u
    ⟨le_rfl, zero_le_one⟩

/-- The root U is concave on its closed variance interval. Its domain may
collapse to a singleton; no division by the total variance is used. -/
theorem concaveOn_parisiRootU
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (ha : 0 ≤ deriv ξ (qs 0) - deriv ξ 0) :
    ConcaveOn ℝ (Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0))
      (parisiRootU μh ξ ms qs) := by
  rcases eq_or_lt_of_le ha with ha | ha
  · rw [← ha]
    refine ⟨convex_Icc _ _, fun u hu v hv s t hs ht hst => ?_⟩
    have hu0 : u = 0 := le_antisymm hu.2 hu.1
    have hv0 : v = 0 := le_antisymm hv.2 hv.1
    simp [hu0, hv0, parisiRootU_zero]
  · obtain ⟨hA, hb⟩ := parisiRootSuffix_spatial_regular_four ξ ms qs
    have hLip := abs_parisiRootSuffix_sub_le ξ ms qs
    have hint : ∀ v ∈ Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0),
        Integrable (fun h => (1 : ℝ) * coleHopfSplitMassResponse 0
          (deriv ξ (qs 0) - deriv ξ 0) (parisiRootSuffix ξ ms qs) h v) μh := by
      intro v hv
      simpa only [one_mul, id_eq] using
        integrable_coleHopfSplitMassResponse_comp (μ := μh) measurable_id
          hA.continuous.measurable hLip (m := 0) ⟨le_rfl, zero_le_one⟩ _ v
    have hconc : ∀ᵐ h ∂μh, ConcaveOn ℝ
        (Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0))
        (coleHopfSplitMassResponse 0 (deriv ξ (qs 0) - deriv ξ 0)
          (parisiRootSuffix ξ ms qs) h) := by
      exact .of_forall fun h => by
        rw [coleHopfSplitMassResponse_eq]
        exact Aristotle.concaveOn_splitMassResponse hA hb ⟨le_rfl, zero_le_one⟩ ha h
    have hi := Aristotle.concaveOn_integral_weighted (μ := μh) (W := fun _ => (1 : ℝ))
      (F := fun h v => coleHopfSplitMassResponse 0 (deriv ξ (qs 0) - deriv ξ 0)
        (parisiRootSuffix ξ ms qs) h v) (.of_forall fun _ => zero_le_one) hconc hint
    unfold parisiRootU
    simpa only [one_mul, smul_eq_mul] using ConcaveOn.smul (c := (2 : ℝ)) (by norm_num) hi

/-- The initial-interval variation function f of (14.238), in overlap rather
than variance coordinates. Its half is the inserted-mass derivative. -/
noncomputable def parisiRootf (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (u : ℝ) : ℝ :=
  parisiRootU μh ξ ms qs (deriv ξ (qs 0) - deriv ξ u) -
    (parisiTheta ξ (qs 0) - parisiTheta ξ u)

/-- The right endpoint has f(q₁)=0 in (14.241), for every field law. -/
theorem parisiRootf_right_endpoint (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) : parisiRootf μh ξ ms qs (qs 0) = 0 := by
  simp only [parisiRootf, sub_self, parisiRootU_zero]

/-- The profile derivative maps every admissible root overlap to the closed
variance interval on which U is differentiated. -/
theorem mapsTo_parisiRoot_variance_coordinate {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    MapsTo (fun u => deriv ξ q - deriv ξ u) (Icc (0 : ℝ) q)
      (Icc (0 : ℝ) (deriv ξ q - deriv ξ 0)) := by
  intro u hu
  have humem : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans hq.2⟩
  refine ⟨sub_nonneg.2 (hξ.strictMonoOn_deriv.monotoneOn humem hq hu.2), ?_⟩
  exact sub_le_sub_left
    (hξ.strictMonoOn_deriv.monotoneOn ⟨le_rfl, zero_le_one⟩ humem hu.1) _

/-- Differentiate the actual f on [0,q₁] in (14.240). Endpoint derivatives
are admissible one-sided derivatives, including when ξ''(0) vanishes. -/
theorem hasDerivWithinAt_parisiRootf
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hq : qs 0 ∈ Icc (0 : ℝ) 1) (hqpos : 0 < qs 0) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (qs 0)) :
    HasDerivWithinAt (parisiRootf μh ξ ms qs)
      (deriv (deriv ξ) u * (u - parisiRootUSpatialMoment 1 μh ξ ms qs
        (deriv ξ (qs 0) - deriv ξ u))) (Icc (0 : ℝ) (qs 0)) u := by
  have humem : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans hq.2⟩
  have hmaps := mapsTo_parisiRoot_variance_coordinate hξ hq
  have ha : 0 < deriv ξ (qs 0) - deriv ξ 0 := sub_pos.2
    (hξ.strictMonoOn_deriv ⟨le_rfl, zero_le_one⟩ hq hqpos)
  have hdv := (hξ.hasDeriv_deriv u humem).const_sub (deriv ξ (qs 0))
  have hU := (hasDerivWithinAt_parisiRootU (μh := μh) ξ ms qs ha (hmaps hu)).comp u
    hdv.hasDerivWithinAt hmaps
  have hθ := (hasDerivAt_parisiTheta (hξ.hasDeriv u humem)
    (hξ.hasDeriv_deriv u humem)).const_sub (parisiTheta ξ (qs 0))
  unfold parisiRootf
  convert hU.sub hθ.hasDerivWithinAt using 1 <;> first | rfl | ring

/-- For the original q-minimizer, f'(q₁)=0 follows from the concrete
stationary moment, completing the root endpoint identities of (14.241). -/
theorem hasDerivWithinAt_parisiRootf_right_endpoint_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    HasDerivWithinAt (parisiRootf μh ξ ms qs) 0 (Icc (0 : ℝ) (qs 0)) (qs 0) := by
  have hqpos := randomFieldParisiQ_first_pos_of_isMin ms qs hμ.integrable_id hm hξ hμ hmin
  have hd := hasDerivWithinAt_parisiRootf (μh := μh) hξ ms qs (hmin.1.mem_Icc 0) hqpos
    (u := qs 0) ⟨hqpos.le, le_rfl⟩
  have hstat := (randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
    ms qs hm hξ hμ hmin).2 0
  simpa only [sub_self, parisiRootUSpatialMoment_one_zero_eq_randomFieldParisiQMoment
    μh ξ ms qs hm, ← hstat, mul_zero] using hd

/-- Derivative form of the root endpoint identity f'(q₁)=0. -/
theorem derivWithin_parisiRootf_right_endpoint_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    derivWithin (parisiRootf μh ξ ms qs) (Icc (0 : ℝ) (qs 0)) (qs 0) = 0 := by
  have hqpos := randomFieldParisiQ_first_pos_of_isMin ms qs hμ.integrable_id hm hξ hμ hmin
  exact (hasDerivWithinAt_parisiRootf_right_endpoint_of_isMin ms qs hm hξ hμ hmin).derivWithin
    (uniqueDiffOn_Icc hqpos (qs 0) ⟨hqpos.le, le_rfl⟩)

/-- Extended overlaps preceding a nonroot insertion are unchanged. -/
theorem qExt_splitParisiOverlap_before {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (u : ℝ)
    {r : ℕ} (hr : r ≤ p.val + 1) : qExt (splitParisiOverlap qs p u) r = qExt qs r := by
  have he := qExt_eraseParisiOverlap (splitParisiOverlap qs p u) p r
  rw [erase_splitParisiOverlap, ite_eq_left hr] at he
  exact he.symm

/-- Extended overlaps following a nonroot insertion shift by one. -/
theorem qExt_splitParisiOverlap_after {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (u : ℝ)
    {r : ℕ} (hr : p.val + 1 < r) :
    qExt (splitParisiOverlap qs p u) (r + 1) = qExt qs r := by
  have he := qExt_eraseParisiOverlap (splitParisiOverlap qs p u) p r
  rw [erase_splitParisiOverlap, ite_eq_right (by omega)] at he
  exact he.symm

/-- The newly inserted extended overlap is the actual free parameter. -/
theorem qExt_splitParisiOverlap_inserted {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (u : ℝ) :
    qExt (splitParisiOverlap qs p u) (p.val + 2) = u := by
  rw [show p.val + 2 = p.succ.val + 1 by rfl, qExt_succ_of_lt _ p.succ.isLt]
  exact Fin.insertNth_apply_same _ _ _

/-- Gaussian intervals before the nonroot split retain their variance. -/
theorem parisiVar_splitParisiOverlap_before (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (u : ℝ)
    {r : ℕ} (hr : r ≤ p.val) :
    parisiVar ξ (splitParisiOverlap qs p u) r = parisiVar ξ qs r := by
  unfold parisiVar
  rw [qExt_splitParisiOverlap_before qs p u (by omega),
    qExt_splitParisiOverlap_before qs p u (by omega)]

/-- Gaussian intervals after the nonroot split shift by one. -/
theorem parisiVar_splitParisiOverlap_after (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (u : ℝ)
    {r : ℕ} (hr : p.val + 1 < r) :
    parisiVar ξ (splitParisiOverlap qs p u) (r + 1) = parisiVar ξ qs r := by
  unfold parisiVar
  rw [qExt_splitParisiOverlap_after qs p u (by omega),
    qExt_splitParisiOverlap_after qs p u hr]

/-- The outer piece of a nonroot split has the left variance increment. -/
theorem parisiVar_splitParisiOverlap_left (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (u : ℝ) :
    parisiVar ξ (splitParisiOverlap qs p u) (p.val + 1) =
      (deriv ξ u - deriv ξ (qs p)).toNNReal := by
  unfold parisiVar
  rw [show p.val + 1 + 1 = p.val + 2 by omega, qExt_splitParisiOverlap_inserted,
    qExt_splitParisiOverlap_before qs p u (by omega), qExt_succ_of_lt qs p.isLt]

/-- The inner piece of a nonroot split has the right variance increment. -/
theorem parisiVar_splitParisiOverlap_right (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (u : ℝ) :
    parisiVar ξ (splitParisiOverlap qs p u) (p.val + 2) =
      (deriv ξ (qExt qs (p.val + 2)) - deriv ξ u).toNNReal := by
  unfold parisiVar
  rw [qExt_splitParisiOverlap_after qs p u (by omega), qExt_splitParisiOverlap_inserted]

/-- Extended masses before a right-mass insertion retain their coordinates. -/
theorem mExt_splitParisiMassRight_before {k : ℕ}
    (ms : Fin k → ℝ) (p : Fin k) (m : ℝ) {r : ℕ} (hr : r ≤ p.val + 1) :
    mExt (splitParisiMassRight ms p m) r = mExt ms r := by
  have he := mExt_eraseParisiMass (splitParisiMassRight ms p m) p.succ r
  rw [erase_splitParisiMassRight, Fin.val_succ, ite_eq_left hr] at he
  exact he.symm

/-- Extended masses after a right-mass insertion shift by one. -/
theorem mExt_splitParisiMassRight_after {k : ℕ}
    (ms : Fin k → ℝ) (p : Fin k) (m : ℝ) {r : ℕ} (hr : p.val + 1 < r) :
    mExt (splitParisiMassRight ms p m) (r + 1) = mExt ms r := by
  have he := mExt_eraseParisiMass (splitParisiMassRight ms p m) p.succ r
  rw [erase_splitParisiMassRight, Fin.val_succ, ite_eq_right (by omega)] at he
  exact he.symm

/-- The inserted inner mass is the freely varied array coordinate. -/
theorem mExt_splitParisiMassRight_inserted {k : ℕ}
    (ms : Fin k → ℝ) (p : Fin k) (m : ℝ) :
    mExt (splitParisiMassRight ms p m) (p.val + 2) = m := by
  rw [show p.val + 2 = p.succ.val + 1 by rfl, mExt_val_succ _ p.succ]
  exact Fin.insertNth_apply_same _ _ _

/-- The actual nonroot recursion split in (14.236): the old outer mass
acts on [q_{r-1},u], and the freely varied inner mass acts on [u,q_r].
All preceding layers, the field translation, and the suffix are explicit. -/
theorem closedParisiX₀_split_right_eq (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (m u h : ℝ) :
    closedParisiX₀ ξ (splitParisiMassRight ms p m)
        (splitParisiOverlap qs p.castSucc u) h =
      ∫ z₀, coleHopfIterate p.val (parisiMassPrefixMasses ms p)
        (parisiMassPrefixVars ξ qs p)
        (coleHopf (ms p) (deriv ξ u - deriv ξ (qs p.castSucc)).toNNReal
          (coleHopf m (deriv ξ (qs p.succ) - deriv ξ u).toNNReal
            (parisiQSuffix ξ 0 ms qs p.castSucc))) (h + z₀)
        ∂gaussianReal 0 (parisiVar ξ qs 0) := by
  have hn : k + 2 = p.val + (2 + (k - p.val)) := by omega
  have hi : coleHopfIterate (k + 2) (parisiLevelMasses (splitParisiMassRight ms p m))
      (parisiLevelVars ξ (splitParisiOverlap qs p.castSucc u)) (parisiLogCoshTerminal 0) =
      coleHopfIterate p.val (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p)
        (coleHopf (ms p) (deriv ξ u - deriv ξ (qs p.castSucc)).toNNReal
          (coleHopf m (deriv ξ (qs p.succ) - deriv ξ u).toNNReal
            (parisiQSuffix ξ 0 ms qs p.castSucc))) := by
    rw [coleHopfIterate_split_two_of_eq p.val (k - p.val) hn]
    congr 4
    · funext r
      rw [parisiLevelMasses_apply]
      change mExt (splitParisiMassRight ms p m) (r.val + 1) = ms ⟨r.val, by omega⟩
      rw [mExt_splitParisiMassRight_before ms p m (by omega)]
      exact mExt_val_succ ms (⟨r.val, by omega⟩ : Fin k)
    · funext r
      unfold parisiLevelVars parisiMassPrefixVars
      exact parisiVar_splitParisiOverlap_before ξ qs p.castSucc u (by
        simp only [Fin.val_castSucc]
        omega)
    · rw [parisiLevelMasses_apply]
      change mExt (splitParisiMassRight ms p m) (p.val + 1) = ms p
      rw [mExt_splitParisiMassRight_before ms p m (by omega)]
      exact mExt_val_succ ms p
    · unfold parisiLevelVars
      exact parisiVar_splitParisiOverlap_left ξ qs p.castSucc u
    · rw [parisiLevelMasses_apply]
      exact mExt_splitParisiMassRight_inserted ms p m
    · unfold parisiLevelVars
      rw [show p.val + 1 + 1 = p.castSucc.val + 2 by rfl,
        parisiVar_splitParisiOverlap_right]
      have hq : qExt qs (p.castSucc.val + 2) = qs p.succ := by
        change qExt qs (p.succ.val + 1) = qs p.succ
        exact qExt_succ_of_lt qs p.succ.isLt
      rw [hq]
    · funext r
      rw [parisiLevelMasses_apply]
      change mExt (splitParisiMassRight ms p m) (p.val + r.val + 2 + 1) =
        mExt ms (p.val + r.val + 2)
      exact mExt_splitParisiMassRight_after ms p m (by omega)
    · funext r
      unfold parisiLevelVars parisiQSuffixVars
      change parisiVar ξ (splitParisiOverlap qs p.castSucc u) (p.val + r.val + 2 + 1) =
        parisiVar ξ qs (p.val + r.val + 2)
      exact parisiVar_splitParisiOverlap_after ξ qs p.castSucc u (by
        simp only [Fin.val_castSucc]
        omega)
  rw [closedParisiX₀_translate, coleHopfIterate_succ]
  change coleHopf 0 (parisiVar ξ (splitParisiOverlap qs p.castSucc u) 0)
    (coleHopfIterate (k + 2) (parisiLevelMasses (splitParisiMassRight ms p m))
      (parisiLevelVars ξ (splitParisiOverlap qs p.castSucc u)) (parisiLogCoshTerminal 0)) h = _
  rw [hi, parisiVar_splitParisiOverlap_before ξ qs p.castSucc u (by omega), coleHopf_zero]

/-- The nonroot U in (14.238), averaged over the independent field/root
product law and the unchanged baseline prefix. -/
noncomputable def parisiRightU (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (v : ℝ) : ℝ :=
  2 * ∫ hz : ℝ × ℝ, coleHopfIterateSplitMassResponse
    (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p) (ms p)
    (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))
    (parisiQSuffix ξ 0 ms qs p.castSucc) (hz.1 + hz.2) v
    ∂μh.prod (gaussianReal 0 (parisiVar ξ qs 0))

/-- The actual first and second moments governing the nonroot U. -/
noncomputable def parisiRightUSpatialMoment (j : ℕ) (μh : Measure ℝ)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (p : Fin k) (v : ℝ) : ℝ :=
  ∫ hz : ℝ × ℝ, coleHopfIterateSplitSpatialMoment j
    (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p) (ms p)
    (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))
    (parisiQSuffix ξ 0 ms qs p.castSucc) (hz.1 + hz.2) v
    ∂μh.prod (gaussianReal 0 (parisiVar ξ qs 0))

/-- Every admissible nonroot overlap gives an admissible variance split. -/
theorem mapsTo_parisi_variance_coordinate {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {qL qR : ℝ} (hL : qL ∈ Icc (0 : ℝ) 1) (hR : qR ∈ Icc (0 : ℝ) 1) :
    MapsTo (fun u => deriv ξ qR - deriv ξ u) (Icc qL qR)
      (Icc (0 : ℝ) (deriv ξ qR - deriv ξ qL)) := by
  intro u hu
  have humem : u ∈ Icc (0 : ℝ) 1 := ⟨hL.1.trans hu.1, hu.2.trans hR.2⟩
  refine ⟨sub_nonneg.2 (hξ.strictMonoOn_deriv.monotoneOn humem hR hu.2), ?_⟩
  exact sub_le_sub_left (hξ.strictMonoOn_deriv.monotoneOn hL humem hu.1) _

private theorem integrable_one_lipschitz_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hHm : Measurable H) (hH : Integrable H μ)
    {A : ℝ → ℝ} (hLip : ∀ x y, |A y - A x| ≤ |y - x|) :
    Integrable (fun ω => A (H ω)) μ := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using hLip
  refine ((integrable_const |A 0|).add hH.abs).mono'
    ((lipschitzWith_toNNReal_of_abs_sub_le hL).continuous.measurable.comp hHm).aestronglyMeasurable
    (.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  have hb := hLip 0 (H ω)
  have ha := abs_sub_abs_le_abs_sub (A (H ω)) (A 0)
  simp only [Pi.add_apply]
  simp only [sub_zero] at hb
  linarith

/-- Differentiate the actual averaged nonroot root value at its matching
inner mass. Fubini is justified by the Lipschitz input and first field moment. -/
theorem hasDerivAt_integral_closedParisiX₀_split_right_mass
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {u : ℝ}
    (hu : u ∈ Icc (qs p.castSucc) (qs p.succ)) :
    HasDerivAt
      (fun b => ∫ h, closedParisiX₀ ξ (splitParisiMassRight ms p b)
        (splitParisiOverlap qs p.castSucc u) h ∂μh)
      (parisiRightU μh ξ ms qs p (deriv ξ (qs p.succ) - deriv ξ u) / 2) (ms p) := by
  let μ := μh.prod (gaussianReal 0 (parisiVar ξ qs 0))
  let H : ℝ × ℝ → ℝ := fun hz => hz.1 + hz.2
  let a := deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)
  let v := deriv ξ (qs p.succ) - deriv ξ u
  have hHm : Measurable H := measurable_fst.add measurable_snd
  have hzg : HasLinearGrowth id := ⟨0, 1, zero_le_one, by simp⟩
  have hz : Integrable id (gaussianReal 0 (parisiVar ξ qs 0)) :=
    hzg.toHasExpGrowth.integrable_gaussianReal measurable_id.aestronglyMeasurable
  have hH : Integrable H μ := (hμ.comp_fst _).add (hz.comp_snd _)
  have hpos : ∀ r, 0 < parisiMassPrefixMasses ms p r := fun r => hm.2.1 _
  have hle : ∀ r, parisiMassPrefixMasses ms p r ≤ 1 := fun r => (hm.2.2 _).le
  have hA := (parisiQSuffix_spatial_regular_four ξ 0 ms qs p.castSucc).1
  have hLip := abs_parisiQSuffix_sub_le ξ 0 ms qs p.castSucc
  have hv : v ∈ Icc (0 : ℝ) a :=
    mapsTo_parisi_variance_coordinate hξ (hq.mem_Icc p.castSucc) (hq.mem_Icc p.succ) hu
  have hd := hasDerivAt_integral_coleHopfIterate_split_mass_comp_of_pos hHm hH
    (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p) hpos hle
    hA.continuous.measurable hLip (hm.2.1 p) (hm.2.2 p).le hv
  have hleft : a - v = deriv ξ u - deriv ξ (qs p.castSucc) := by dsimp [a, v]; ring
  rw [hleft] at hd
  let F : ℝ → ℝ → ℝ := fun b => coleHopfIterate p.val
    (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p)
    (coleHopf (ms p) (deriv ξ u - deriv ξ (qs p.castSucc)).toNNReal
      (coleHopf b v.toNNReal (parisiQSuffix ξ 0 ms qs p.castSucc)))
  have hF : ∀ b, Integrable (fun hz => F b (H hz)) μ := by
    intro b
    have hL : ∀ x y, |parisiQSuffix ξ 0 ms qs p.castSucc y -
        parisiQSuffix ξ 0 ms qs p.castSucc x| ≤ 1 * |y - x| := by
      simpa only [one_mul] using hLip
    have hB := abs_coleHopf_sub_le_of_lipschitz b hA.continuous.measurable hL v.toNNReal
    have hC := abs_coleHopf_sub_le_of_lipschitz (ms p)
      (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable hB
      (deriv ξ u - deriv ξ (qs p.castSucc)).toNNReal
    apply integrable_one_lipschitz_comp hHm hH
    simpa only [one_mul] using abs_coleHopfIterate_sub_le p.val
      (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p)
      (lipschitzWith_toNNReal_of_abs_sub_le hC).continuous.measurable hC
  have he : (fun b => ∫ h, closedParisiX₀ ξ (splitParisiMassRight ms p b)
      (splitParisiOverlap qs p.castSucc u) h ∂μh) = fun b => ∫ hz, F b (H hz) ∂μ := by
    funext b
    simp only [closedParisiX₀_split_right_eq]
    exact (integral_prod (fun hz => F b (H hz)) (hF b)).symm
  rw [he]
  convert hd using 1
  dsimp [parisiRightU, μ, H, a, v]
  ring

/-- The actual matching-mass derivative in the nonroot split equals half
of U minus its theta correction, as in (14.239). -/
theorem splitParisiRightMassDeriv_eq_U
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {u : ℝ}
    (hu : u ∈ Icc (qs p.castSucc) (qs p.succ)) :
    splitParisiRightMassDeriv μh ξ ms qs p u (ms p) =
      (1 / 2) * (parisiRightU μh ξ ms qs p (deriv ξ (qs p.succ) - deriv ξ u) -
        (parisiTheta ξ (qs p.succ) - parisiTheta ξ u)) := by
  have hpref (i : Fin p.succ.val) :
      splitParisiMassRight ms p 0 ⟨i.val, by omega⟩ = ms ⟨i.val, by omega⟩ :=
    splitParisiMassLeft_apply_of_lt ms p.succ 0 (by exact i.isLt)
  have hmp : ms p ∈ Icc (0 : ℝ) 1 := ⟨(hm.2.1 p).le, (hm.2.2 p).le⟩
  have hold := hasDerivWithinAt_randomFieldParisiX₀_mass_update hμ ξ
    (splitParisiMassRight ms p 0) (splitParisiOverlap qs p.castSucc u) p.succ
    (fun i => by rw [hpref i]; exact hm.2.1 _)
    (fun i => by rw [hpref i]; exact (hm.2.2 _).le) hmp
  simp only [update_splitParisiMassRight] at hold
  have hnew := hasDerivAt_integral_closedParisiX₀_split_right_mass hμ hξ ms qs p hm hq hu
  have hM := (hold.derivWithin (uniqueDiffOn_Icc_zero_one _ hmp)).symm.trans
    (hnew.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one _ hmp))
  have hqu : qExt (splitParisiOverlap qs p.castSucc u) (p.val + 2) = u :=
    qExt_splitParisiOverlap_inserted qs p.castSucc u
  have hqr : qExt (splitParisiOverlap qs p.castSucc u) (p.val + 3) = qs p.succ := by
    rw [show p.val + 3 = (p.val + 2) + 1 by omega,
      qExt_splitParisiOverlap_after qs p.castSucc u (by change p.val + 1 < p.val + 2; omega)]
    exact qExt_succ_of_lt qs p.succ.isLt
  unfold splitParisiRightMassDeriv
  rw [hM, hqr, hqu]
  ring

/-- Formula (14.239) as a one-sided mass derivative of the actual nonroot
split functional, with all recursion and field averages discharged. -/
theorem hasDerivWithinAt_closedRandomFieldParisiFunctional_split_right_mass_eq_U
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {u : ℝ}
    (hu : u ∈ Icc (qs p.castSucc) (qs p.succ)) :
    HasDerivWithinAt
      (fun b => closedRandomFieldParisiFunctional μh ξ
        (splitParisiMassRight ms p b) (splitParisiOverlap qs p.castSucc u))
      ((1 / 2) * (parisiRightU μh ξ ms qs p (deriv ξ (qs p.succ) - deriv ξ u) -
        (parisiTheta ξ (qs p.succ) - parisiTheta ξ u))) (Icc (0 : ℝ) 1) (ms p) := by
  rw [← splitParisiRightMassDeriv_eq_U hμ hξ ms qs p hm hq hu]
  exact hasDerivWithinAt_closedRandomFieldParisiFunctional_split_right_mass hμ ξ ms qs
    hm.2.1 (fun i => (hm.2.2 i).le) p u ⟨(hm.2.1 p).le, (hm.2.2 p).le⟩

/-- The nonroot U vanishes at zero inserted variance. -/
theorem parisiRightU_zero (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) :
    parisiRightU μh ξ ms qs p 0 = 0 := by
  simp only [parisiRightU, coleHopfIterateSplitMassResponse_zero, integral_zero, mul_zero]

/-- U' after the full field, root, and unchanged-prefix averages in (14.240). -/
theorem hasDerivWithinAt_parisiRightU
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) :
    HasDerivWithinAt (parisiRightU μh ξ ms qs p)
      (parisiRightUSpatialMoment 1 μh ξ ms qs p v)
      (Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) v := by
  have hHm : Measurable (fun hz : ℝ × ℝ => hz.1 + hz.2) := measurable_fst.add measurable_snd
  have ha : 0 < deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) := sub_pos.2
    (hξ.strictMonoOn_deriv (hq.mem_Icc p.castSucc) (hq.mem_Icc p.succ)
      (hq.1 (by change p.val < p.val + 1; omega)))
  have hd := hasDerivWithinAt_integral_parisiQSuffix_prefixSplitMassResponse_comp
    (μ := μh.prod (gaussianReal 0 (parisiVar ξ qs 0))) hHm
    (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p)
    (fun r => hm.2.1 _) (fun r => (hm.2.2 _).le) ξ 0 ms qs p.castSucc
    (hm.2.1 p) (hm.2.2 p).le ha hv
  unfold parisiRightU parisiRightUSpatialMoment
  convert hd.const_mul 2 using 1 <;> first | rfl | ring

/-- U'' is minus its actual second spatial moment after all the averages. -/
theorem hasDerivWithinAt_parisiRightUSpatialMoment_one
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) :
    HasDerivWithinAt (parisiRightUSpatialMoment 1 μh ξ ms qs p)
      (-parisiRightUSpatialMoment 2 μh ξ ms qs p v)
      (Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) v := by
  have hHm : Measurable (fun hz : ℝ × ℝ => hz.1 + hz.2) := measurable_fst.add measurable_snd
  have ha : 0 < deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) := sub_pos.2
    (hξ.strictMonoOn_deriv (hq.mem_Icc p.castSucc) (hq.mem_Icc p.succ)
      (hq.1 (by change p.val < p.val + 1; omega)))
  unfold parisiRightUSpatialMoment
  exact hasDerivWithinAt_integral_parisiQSuffix_prefixSplitSpatialMoment_comp
    (μ := μh.prod (gaussianReal 0 (parisiVar ξ qs 0))) hHm
    (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p)
    (fun r => hm.2.1 _) (fun r => (hm.2.2 _).le) ξ 0 ms qs p.castSucc
    (hm.2.1 p) (hm.2.2 p).le ha hv

/-- The suffix at the left overlap retains the one layer which precedes
the suffix at the next overlap. This is the adjacent layer in U'(0). -/
theorem parisiQSuffix_castSucc_eq_coleHopf_succ (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) :
    parisiQSuffix ξ h ms qs p.castSucc =
      coleHopf (mExt ms (p.val + 2)) (parisiVar ξ qs (p.val + 2))
        (parisiQSuffix ξ h ms qs p.succ) := by
  have hn : k - p.castSucc.val = 0 + ((k - p.succ.val) + 1) := by
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  unfold parisiQSuffix
  conv_lhs => rw [coleHopfIterate_split_one_of_eq 0 (k - p.succ.val) hn]
  simp only [coleHopfIterate_zero, parisiQSuffixMasses, parisiQSuffixVars,
    Fin.val_castSucc, Fin.val_succ, zero_add]
  congr 3
  · funext r
    apply congrArg (mExt ms)
    simp only [Fin.val_succ]
    omega
  · funext r
    apply congrArg (parisiVar ξ qs)
    simp only [Fin.val_succ]
    omega

/-- The inner derivative of the old q-moment is the actual derivative of
the adjacent suffix. It is proved from the positive-mass recursion. -/
theorem deriv_parisiQSuffix_castSucc_eq_integral_succ
    (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (p : Fin k) (hm : ParisiMAdmissible ms) (x : ℝ) :
    deriv (parisiQSuffix ξ h ms qs p.castSucc) x =
      ∫ w, parisiQSuffixDeriv ξ h ms qs p.succ (x + w) *
        coleHopfQ (mExt ms (p.val + 2)) (parisiVar ξ qs (p.val + 2))
          (parisiQSuffix ξ h ms qs p.succ) x w
        ∂gaussianReal 0 (parisiVar ξ qs (p.val + 2)) := by
  obtain ⟨hA, C, hA', _, hA'b, _⟩ := parisiQSuffix_deriv_regular (ξ := ξ) (h := h) qs p.succ hm
  have hAg := HasLinearGrowth.of_bounded_deriv hA hA'b
  have hA'g := HasExpGrowth.of_bounded hA'b
  have hmass : mExt ms (p.val + 2) ≠ 0 := (hm.mExt_pos (by omega)).ne'
  rw [parisiQSuffix_castSucc_eq_coleHopf_succ]
  exact (hasDerivAt_coleHopf hA hAg hA'g (measurable_of_hasDerivAt hA') hmass _ x).deriv

/-- The old local q-moment is the initial spatial moment of the mass
response. The adjacent suffix layer and field translation are retained. -/
theorem coleHopfSplitMoment_succ_eq_splitSpatialMoment_zero
    (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (p : Fin k) (hm : ParisiMAdmissible ms) (x : ℝ) :
    coleHopfSplitMoment (mExt ms (p.val + 2)) (ms p) (parisiVar ξ qs (p.val + 2))
        (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)).toNNReal
        (parisiQSuffix ξ h ms qs p.succ) (parisiQSuffixDeriv ξ h ms qs p.succ) x =
      coleHopfSplitSpatialMoment 1 (ms p) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))
        (parisiQSuffix ξ 0 ms qs p.castSucc) (h + x) 0 := by
  have hzero : coleHopf (ms p) (0 : ℝ≥0) (parisiQSuffix ξ 0 ms qs p.castSucc) =
      parisiQSuffix ξ 0 ms qs p.castSucc := funext fun y => coleHopf_zero_var _ _ y
  have hAt : parisiQSuffix ξ h ms qs p.castSucc =
      fun y => parisiQSuffix ξ 0 ms qs p.castSucc (h + y) :=
    funext fun y => parisiQSuffix_translate ξ h ms qs p.castSucc y
  have hDh := (parisiQSuffix_deriv_regular (ξ := ξ) (h := h) qs p.castSucc hm).1
  have hD₀ := (parisiQSuffix_deriv_regular (ξ := ξ) (h := 0) qs p.castSucc hm).1
  have hDt : ∀ y, deriv (parisiQSuffix ξ h ms qs p.castSucc) y =
      deriv (parisiQSuffix ξ 0 ms qs p.castSucc) (h + y) := by
    intro y
    rw [(hDh y).deriv, (hD₀ (h + y)).deriv]
    exact parisiQSuffixDeriv_translate ξ h ms qs p.castSucc y
  unfold coleHopfSplitMoment coleHopfSplitSpatialMoment
  simp only [Real.toNNReal_zero, sub_zero, hzero, iteratedDeriv_one]
  rw [← parisiQSuffix_castSucc_eq_coleHopf_succ]
  apply integral_congr_ae (.of_forall fun z => ?_)
  rw [← deriv_parisiQSuffix_castSucc_eq_integral_succ ξ h ms qs p hm, hDt,
    hAt, coleHopfQ_translate]
  simp only [add_assoc]

/-- The full old q-moment is the initial response moment transported through
the unchanged prefix and root Gaussian, with its field translation explicit. -/
theorem parisiQMoment_succ_eq_integral_prefixSplitSpatialMoment_zero
    (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (p : Fin k) (hm : ParisiMAdmissible ms) :
    parisiQMoment ξ h ms qs p.succ =
      ∫ z₀, coleHopfIterateSplitSpatialMoment 1 (parisiMassPrefixMasses ms p)
        (parisiMassPrefixVars ξ qs p) (ms p)
        (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))
        (parisiQSuffix ξ 0 ms qs p.castSucc) (h + z₀) 0
        ∂gaussianReal 0 (parisiVar ξ qs 0) := by
  have hpm : parisiQPrefixMasses ms p.succ = parisiMassPrefixMasses ms p := by
    funext r
    change mExt ms (r.val + 1) = ms ⟨r.val, by omega⟩
    exact mExt_val_succ ms (⟨r.val, by omega⟩ : Fin k)
  have hqL : qExt qs p.succ.val = qs p.castSucc :=
    qExt_succ_of_lt qs p.castSucc.isLt
  have hmL : mExt ms p.succ.val = ms p := mExt_val_succ ms p
  have hvR : (deriv ξ (qExt qs (p.succ.val + 2)) - deriv ξ (qs p.succ)).toNNReal =
      parisiVar ξ qs (p.val + 2) := by
    unfold parisiVar
    change _ = (deriv ξ (qExt qs (p.succ.val + 2)) - deriv ξ (qExt qs (p.succ.val + 1))).toNNReal
    rw [qExt_succ_of_lt qs p.succ.isLt]
  let a := deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)
  have hGh : ∀ x, coleHopf (ms p) a.toNNReal
      (coleHopf (mExt ms (p.val + 2)) (parisiVar ξ qs (p.val + 2))
        (parisiQSuffix ξ h ms qs p.succ)) x =
      coleHopf (ms p) a.toNNReal (parisiQSuffix ξ 0 ms qs p.castSucc) (h + x) := by
    intro x
    rw [← parisiQSuffix_castSucc_eq_coleHopf_succ]
    have hAt : parisiQSuffix ξ h ms qs p.castSucc =
        fun y => parisiQSuffix ξ 0 ms qs p.castSucc (h + y) :=
      funext fun y => parisiQSuffix_translate ξ h ms qs p.castSucc y
    rw [hAt, coleHopf_translate]
  unfold parisiQMoment
  rw [ite_eq_right (by simp only [Fin.val_succ]; omega), hqL, hmL, hvR, hpm]
  change (∫ z₀, ∫ zs, coleHopfSplitMoment (mExt ms (p.val + 2)) (ms p)
      (parisiVar ξ qs (p.val + 2)) a.toNNReal
      (parisiQSuffix ξ h ms qs p.succ) (parisiQSuffixDeriv ξ h ms qs p.succ)
      (z₀ + ∑ r, zs r)
      ∂cascadeTiltMeasure p.val (parisiMassPrefixMasses ms p)
        (fun r => gaussianReal 0 (parisiMassPrefixVars ξ qs p r))
        (fun zs => ENNReal.ofReal (Real.exp
          (coleHopf (ms p) a.toNNReal
            (coleHopf (mExt ms (p.val + 2)) (parisiVar ξ qs (p.val + 2))
              (parisiQSuffix ξ h ms qs p.succ)) (z₀ + ∑ r, zs r))))
      ∂gaussianReal 0 (parisiVar ξ qs 0)) = _
  apply integral_congr_ae (.of_forall fun z₀ => ?_)
  unfold coleHopfIterateSplitSpatialMoment
  simp_rw [hGh]
  dsimp only [a]
  simp_rw [coleHopfSplitMoment_succ_eq_splitSpatialMoment_zero ξ h ms qs p hm]
  simp only [add_assoc]

/-- Fubini identifies the initial nonroot U' moment with the old random-field
q-moment. Its integrability follows from the actual spatial moment bounds. -/
theorem parisiRightUSpatialMoment_one_zero_eq_randomFieldParisiQMoment
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) :
    parisiRightUSpatialMoment 1 μh ξ ms qs p 0 = randomFieldParisiQMoment μh ξ ms qs p.succ := by
  have hHm : Measurable (fun hz : ℝ × ℝ => hz.1 + hz.2) := measurable_fst.add measurable_snd
  have hpos : ∀ r, 0 < parisiMassPrefixMasses ms p r := fun r => hm.2.1 _
  have hle : ∀ r, parisiMassPrefixMasses ms p r ≤ 1 := fun r => (hm.2.2 _).le
  obtain ⟨hA, C, hC⟩ := parisiQSuffix_spatial_regular_four ξ 0 ms qs p.castSucc
  have hLip := abs_parisiQSuffix_sub_le ξ 0 ms qs p.castSucc
  let a := deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)
  have ha : 0 < a := sub_pos.2
    (hξ.strictMonoOn_deriv (hq.mem_Icc p.castSucc) (hq.mem_Icc p.succ)
      (hq.1 (by change p.val < p.val + 1; omega)))
  have hmeas := measurable_coleHopfIterateSplitSpatialMoment_one_of_pos
    (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p) hpos hle
    hA ⟨C, hC⟩ hLip (hm.2.1 p) (hm.2.2 p).le ha (v := 0) ⟨le_rfl, ha.le⟩
  have hint : Integrable (fun hz : ℝ × ℝ => coleHopfIterateSplitSpatialMoment 1
      (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p) (ms p) a
      (parisiQSuffix ξ 0 ms qs p.castSucc) (hz.1 + hz.2) 0)
      (μh.prod (gaussianReal 0 (parisiVar ξ qs 0))) := by
    refine Integrable.of_bound (hmeas.comp hHm).aestronglyMeasurable (C ^ 2)
      (.of_forall fun hz => ?_)
    rw [Real.norm_eq_abs]
    exact (coleHopfIterateSplitSpatialMoment_one_two_bounds
      (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p) hpos hle
      hA hC hLip ⟨(hm.2.1 p).le, (hm.2.2 p).le⟩ a 0 (hz.1 + hz.2)).1
  unfold parisiRightUSpatialMoment randomFieldParisiQMoment
  rw [integral_prod _ hint]
  exact integral_congr_ae (.of_forall fun h =>
    (parisiQMoment_succ_eq_integral_prefixSplitSpatialMoment_zero ξ h ms qs p hm).symm)

/-- U'(0)=q_r for every nonroot interval of the original q-minimizer,
following directly from Proposition 14.7.5 and the actual moment identity. -/
theorem hasDerivWithinAt_parisiRightU_zero_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    HasDerivWithinAt (parisiRightU μh ξ ms qs p) (qs p.succ)
      (Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) 0 := by
  have ha : 0 < deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) := sub_pos.2
    (hξ.strictMonoOn_deriv (hmin.1.mem_Icc p.castSucc) (hmin.1.mem_Icc p.succ)
      (hmin.1.1 (by change p.val < p.val + 1; omega)))
  have hd := hasDerivWithinAt_parisiRightU (μh := μh) hξ ms qs p hm hmin.1
    (v := 0) ⟨le_rfl, ha.le⟩
  have hstat := (randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
    ms qs hm hξ hμ hmin).2 p.succ
  rw [parisiRightUSpatialMoment_one_zero_eq_randomFieldParisiQMoment hξ ms qs p hm hmin.1,
    ← hstat] at hd
  exact hd

/-- Derivative form of U'(0)=q_r on the closed nonroot variance interval. -/
theorem derivWithin_parisiRightU_zero_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    derivWithin (parisiRightU μh ξ ms qs p)
      (Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) 0 = qs p.succ := by
  have ha : 0 < deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) := sub_pos.2
    (hξ.strictMonoOn_deriv (hmin.1.mem_Icc p.castSucc) (hmin.1.mem_Icc p.succ)
      (hmin.1.1 (by change p.val < p.val + 1; omega)))
  exact (hasDerivWithinAt_parisiRightU_zero_of_isMin ms qs p hm hξ hμ hmin).derivWithin
    (uniqueDiffOn_Icc ha 0 ⟨le_rfl, ha.le⟩)

/-- The full nonroot U is concave after the field, root and prefix averages. -/
theorem concaveOn_parisiRightU
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) :
    ConcaveOn ℝ (Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)))
      (parisiRightU μh ξ ms qs p) := by
  have hHm : Measurable (fun hz : ℝ × ℝ => hz.1 + hz.2) := measurable_fst.add measurable_snd
  have ha : 0 ≤ deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) := sub_nonneg.2
    (hξ.strictMonoOn_deriv.monotoneOn (hq.mem_Icc p.castSucc) (hq.mem_Icc p.succ)
      (hq.monotone (by change p.val ≤ p.val + 1; omega)))
  have hc := concaveOn_integral_parisiQSuffix_prefixSplitMassResponse_comp
    (μ := μh.prod (gaussianReal 0 (parisiVar ξ qs 0))) hHm
    (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p)
    (fun r => hm.2.1 _) (fun r => (hm.2.2 _).le) ξ 0 ms qs p.castSucc
    (hm.2.1 p) (hm.2.2 p).le ha
  unfold parisiRightU
  simpa only [smul_eq_mul] using ConcaveOn.smul (c := (2 : ℝ)) (by norm_num) hc

/-- The nonroot f of (14.238), in the original overlap coordinate. -/
noncomputable def parisiRightf (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (u : ℝ) : ℝ :=
  parisiRightU μh ξ ms qs p (deriv ξ (qs p.succ) - deriv ξ u) -
    (parisiTheta ξ (qs p.succ) - parisiTheta ξ u)

/-- The nonroot endpoint has f(q_r)=0, independently of minimization. -/
theorem parisiRightf_right_endpoint (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) :
    parisiRightf μh ξ ms qs p (qs p.succ) = 0 := by
  simp only [parisiRightf, sub_self, parisiRightU_zero]

/-- The actual f derivative in (14.240) on its closed overlap interval. -/
theorem hasDerivWithinAt_parisiRightf
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {u : ℝ}
    (hu : u ∈ Icc (qs p.castSucc) (qs p.succ)) :
    HasDerivWithinAt (parisiRightf μh ξ ms qs p)
      (deriv (deriv ξ) u * (u - parisiRightUSpatialMoment 1 μh ξ ms qs p
        (deriv ξ (qs p.succ) - deriv ξ u))) (Icc (qs p.castSucc) (qs p.succ)) u := by
  have humem : u ∈ Icc (0 : ℝ) 1 :=
    ⟨(hq.mem_Icc p.castSucc).1.trans hu.1, hu.2.trans (hq.mem_Icc p.succ).2⟩
  have hmaps := mapsTo_parisi_variance_coordinate hξ (hq.mem_Icc p.castSucc) (hq.mem_Icc p.succ)
  have hdv := (hξ.hasDeriv_deriv u humem).const_sub (deriv ξ (qs p.succ))
  have hU := (hasDerivWithinAt_parisiRightU (μh := μh) hξ ms qs p hm hq (hmaps hu)).comp u
    hdv.hasDerivWithinAt hmaps
  have hθ := (hasDerivAt_parisiTheta (hξ.hasDeriv u humem)
    (hξ.hasDeriv_deriv u humem)).const_sub (parisiTheta ξ (qs p.succ))
  unfold parisiRightf
  convert hU.sub hθ.hasDerivWithinAt using 1 <;> first | rfl | ring

/-- For the q-minimizer, f'(q_r)=0 is a consequence of its original stationary
moment and the actual response, including the admissible endpoint derivative. -/
theorem hasDerivWithinAt_parisiRightf_right_endpoint_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    HasDerivWithinAt (parisiRightf μh ξ ms qs p) 0
      (Icc (qs p.castSucc) (qs p.succ)) (qs p.succ) := by
  have hd := hasDerivWithinAt_parisiRightf (μh := μh) hξ ms qs p hm hmin.1
    (u := qs p.succ) ⟨hmin.1.monotone (by change p.val ≤ p.val + 1; omega), le_rfl⟩
  have hstat := (randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
    ms qs hm hξ hμ hmin).2 p.succ
  simpa only [sub_self, parisiRightUSpatialMoment_one_zero_eq_randomFieldParisiQMoment
    hξ ms qs p hm hmin.1, ← hstat, mul_zero] using hd

/-- Derivative form of the nonroot f endpoint identity (14.241). -/
theorem derivWithin_parisiRightf_right_endpoint_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    derivWithin (parisiRightf μh ξ ms qs p) (Icc (qs p.castSucc) (qs p.succ)) (qs p.succ) = 0 := by
  have hqr : qs p.castSucc < qs p.succ := hmin.1.1 (by change p.val < p.val + 1; omega)
  exact (hasDerivWithinAt_parisiRightf_right_endpoint_of_isMin ms qs p hm hξ hμ hmin).derivWithin
    (uniqueDiffOn_Icc hqr (qs p.succ) ⟨hqr.le, le_rfl⟩)

/-- At the left endpoint, the empty outer interval leaves exactly the old
mass-coordinate variation in the actual closed recursion. -/
theorem closedParisiX₀_split_right_left_endpoint_eq_mass_update
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (p : Fin k) (m h : ℝ) :
    closedParisiX₀ ξ (splitParisiMassRight ms p m)
        (splitParisiOverlap qs p.castSucc (qs p.castSucc)) h =
      closedParisiX₀ ξ (Function.update ms p m) qs h := by
  have hv : parisiVar ξ qs (p.val + 1) =
      (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)).toNNReal := by
    unfold parisiVar
    change (deriv ξ (qExt qs (p.succ.val + 1)) - deriv ξ (qExt qs (p.castSucc.val + 1))).toNNReal = _
    rw [qExt_succ_of_lt qs p.succ.isLt, qExt_succ_of_lt qs p.castSucc.isLt]
  have hzero : coleHopf (ms p) (0 : ℝ≥0)
      (coleHopf m (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)).toNNReal
        (parisiQSuffix ξ 0 ms qs p.castSucc)) =
      coleHopf m (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)).toNNReal
        (parisiQSuffix ξ 0 ms qs p.castSucc) :=
    funext fun x => coleHopf_zero_var _ _ x
  rw [closedParisiX₀_split_right_eq, closedParisiX₀_mass_update_eq, hv]
  simp only [sub_self, Real.toNNReal_zero, hzero]

/-- For the fixed-level MIN, f(q_{r-1})=0 in (14.242). The argument uses
mass minimality at the original level count and proves the endpoint bridge. -/
theorem parisiRightf_left_endpoint_eq_zero_of_isMinOn
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hmin : IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain k) (ms, qs)) :
    parisiRightf μh ξ ms qs p (qs p.castSucc) = 0 := by
  have hmp : ms p ∈ Icc (0 : ℝ) 1 := ⟨(hm.2.1 p).le, (hm.2.2 p).le⟩
  have hold := hasDerivWithinAt_randomFieldParisiX₀_mass_update hμ ξ ms qs p
    (fun r => hm.2.1 _) (fun r => (hm.2.2 _).le) hmp
  have hnew := hasDerivAt_integral_closedParisiX₀_split_right_mass hμ hξ ms qs p hm hq
    (u := qs p.castSucc) ⟨le_rfl, hq.monotone (by change p.val ≤ p.val + 1; omega)⟩
  have he : (fun b => ∫ h, closedParisiX₀ ξ (splitParisiMassRight ms p b)
      (splitParisiOverlap qs p.castSucc (qs p.castSucc)) h ∂μh) =
      fun b => ∫ h, closedParisiX₀ ξ (Function.update ms p b) qs h ∂μh := by
    funext b
    exact integral_congr_ae (.of_forall fun h =>
      closedParisiX₀_split_right_left_endpoint_eq_mass_update ξ ms qs p b h)
  rw [he] at hnew
  have hM := (hold.derivWithin (uniqueDiffOn_Icc_zero_one _ hmp)).symm.trans
    (hnew.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one _ hmp))
  have hqmem : qs ∈ parisiOverlapDomain k :=
    mem_parisiOverlapDomain_iff.2 ⟨hq.monotone, hq.2.1, hq.2.2⟩
  have hstat := randomFieldParisiMassMoment_sub_theta_eq_zero_of_isMinOn hμ ξ ms qs p hm hqmem hmin
  have hqL : qExt qs (p.val + 1) = qs p.castSucc := qExt_succ_of_lt qs p.castSucc.isLt
  have hqR : qExt qs (p.val + 2) = qs p.succ := qExt_succ_of_lt qs p.succ.isLt
  rw [hM, hqL, hqR] at hstat
  unfold parisiRightf
  linarith

end SpinGlass
