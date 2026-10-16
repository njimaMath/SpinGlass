import SpinGlass.Parisi.Variational.ParisiOuterSplitResponse
import SpinGlass.Parisi.Variational.ParisiCascadeTransport

/-!
# Initial moments of the outer Parisi split

The initial outer moment is the old q-moment, including the first and last
overlaps. The last Gaussian mark is transported through its actual cascade
weight. This identifies the mirror U'(0) in Section 14.9 without an assumed
stationary moment or a two-sided derivative at zero variance.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- The initial inner spatial moment uses the unchanged suffix derivative. -/
theorem coleHopfSplitSpatialMoment_zero_eq (s : ℕ) (m a : ℝ)
    (A : ℝ → ℝ) (x : ℝ) :
    coleHopfSplitSpatialMoment s m a A x 0 =
      ∫ z, (iteratedDeriv s A (x + z)) ^ 2 * coleHopfQ m a.toNNReal A x z
        ∂gaussianReal 0 a.toNNReal := by
  have hz : coleHopf m (0 : ℝ≥0) A = A := funext fun y => coleHopf_zero_var m A y
  simp only [coleHopfSplitSpatialMoment, Real.toNNReal_zero, sub_zero, hz]

/-- At zero outer variance, the full matched layer remains inside the
spatial derivative, and no extra Gaussian mark remains outside it. -/
theorem coleHopfIterateOuterSplitSpatialMoment_zero_eq {j : ℕ} (s : ℕ)
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (m a : ℝ) (A : ℝ → ℝ) (x : ℝ) :
    coleHopfIterateOuterSplitSpatialMoment s ms vs m a A x 0 =
      ∫ zs, (iteratedDeriv s (coleHopf m a.toNNReal A) (x + ∑ p, zs p)) ^ 2
        ∂cascadeTiltMeasure j ms (fun p => gaussianReal 0 (vs p))
          (fun zs => ENNReal.ofReal (Real.exp (coleHopf m a.toNNReal A (x + ∑ p, zs p)))) := by
  simp [coleHopfIterateOuterSplitSpatialMoment, coleHopfIterateSplitSpatialMoment,
    coleHopfSplitSpatialMoment, coleHopfQ]

/-- The first positive layer of the root suffix is the matched layer of
the outer split at the first free overlap. -/
theorem parisiRootSuffix_eq_coleHopf_first (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    parisiRootSuffix ξ ms qs = coleHopf (mExt ms 1) (parisiVar ξ qs 1)
      (parisiQSuffix ξ 0 ms qs 0) := by
  unfold parisiRootSuffix parisiQSuffix
  rw [coleHopfIterate_succ]
  simp only [Fin.val_zero, Nat.sub_zero]
  congr 1
  congr 1
  · funext r
    dsimp only [Fin.tail]
    rw [parisiLevelMasses_apply]
    simp [parisiQSuffixMasses, Nat.add_assoc]
  · funext r
    simp [Fin.tail, parisiLevelVars, parisiQSuffixVars, Nat.add_assoc]

/-- The outer prefix at a successor overlap appends the preceding old
mass coordinate. -/
theorem parisiOuterMassPrefixMasses_succ {k : ℕ} (ms : Fin k → ℝ) (r : Fin k) :
    parisiOuterMassPrefixMasses ms r.succ =
      Fin.snoc (parisiMassPrefixMasses ms r) (ms r) := by
  funext p
  refine Fin.lastCases ?_ (fun t => ?_) p
  · simp only [parisiOuterMassPrefixMasses, Fin.val_last, Fin.snoc_last]
    exact mExt_val_succ ms r
  · simp only [parisiOuterMassPrefixMasses, Fin.val_castSucc, Fin.snoc_castSucc,
      parisiMassPrefixMasses]
    exact mExt_val_succ ms (⟨t.val, by omega⟩ : Fin k)

/-- The appended prefix variance is the old interval immediately preceding
the current overlap. -/
theorem parisiOuterMassPrefixVars_succ (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (r : Fin k) :
    parisiOuterMassPrefixVars ξ qs r.succ =
      Fin.snoc (parisiMassPrefixVars ξ qs r) (parisiVar ξ qs (r.val + 1)) := by
  funext p
  refine Fin.lastCases ?_ (fun t => ?_) p
  · simp [parisiOuterMassPrefixVars]
  · simp [parisiOuterMassPrefixVars, parisiMassPrefixVars]

/-- Initial outer moments at successor overlaps are exactly the initial
moments of the preceding inner split. This also transfers second moments. -/
theorem parisiLeftUSpatialMoment_succ_zero_eq_parisiRightUSpatialMoment
    (s : ℕ) (hs : s ∈ Finset.Icc 1 4) (μh : Measure ℝ) (ξ : ℝ → ℝ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin k)
    (hm : ParisiMAdmissible ms) :
    parisiLeftUSpatialMoment s μh ξ ms qs r.succ 0 =
      parisiRightUSpatialMoment s μh ξ ms qs r 0 := by
  have hvR : (deriv ξ (qExt qs (r.succ.val + 2)) - deriv ξ (qs r.succ)).toNNReal =
      parisiVar ξ qs (r.val + 2) := by
    unfold parisiVar
    change _ = (deriv ξ (qExt qs (r.succ.val + 2)) -
      deriv ξ (qExt qs (r.succ.val + 1))).toNNReal
    rw [qExt_succ_of_lt qs r.succ.isLt]
  have hvL : parisiVar ξ qs (r.val + 1) =
      (deriv ξ (qs r.succ) - deriv ξ (qs r.castSucc)).toNNReal := by
    unfold parisiVar
    change (deriv ξ (qExt qs (r.succ.val + 1)) -
      deriv ξ (qExt qs (r.castSucc.val + 1))).toNNReal = _
    rw [qExt_succ_of_lt qs r.castSucc.isLt, qExt_succ_of_lt qs r.succ.isLt]
  obtain ⟨hA, C, hC⟩ := parisiQSuffix_spatial_regular_four ξ 0 ms qs r.castSucc
  have hsc : (s : WithTop ℕ∞) ≤ 4 := by exact_mod_cast (Finset.mem_Icc.1 hs).2
  have hFm := (hA.continuous_iteratedDeriv s hsc).measurable.pow_const 2
  have hFb : ∀ x, |(iteratedDeriv s (parisiQSuffix ξ 0 ms qs r.castSucc) x) ^ 2| ≤ C ^ 2 := by
    intro x
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC s hs x) 2
  unfold parisiLeftUSpatialMoment parisiRightUSpatialMoment
  apply integral_congr_ae (.of_forall fun hz => ?_)
  rw [coleHopfIterateOuterSplitSpatialMoment_zero_eq, hvR]
  change (∫ zs, (iteratedDeriv s
      (coleHopf (mExt ms (r.val + 2)) (parisiVar ξ qs (r.val + 2))
        (parisiQSuffix ξ 0 ms qs r.succ)) (hz.1 + hz.2 + ∑ p, zs p)) ^ 2
      ∂cascadeTiltMeasure (r.val + 1) (parisiOuterMassPrefixMasses ms r.succ)
        (fun p => gaussianReal 0 (parisiOuterMassPrefixVars ξ qs r.succ p))
        (fun zs => ENNReal.ofReal (Real.exp
          (coleHopf (mExt ms (r.val + 2)) (parisiVar ξ qs (r.val + 2))
            (parisiQSuffix ξ 0 ms qs r.succ) (hz.1 + hz.2 + ∑ p, zs p))))) = _
  rw [← parisiQSuffix_castSucc_eq_coleHopf_succ, parisiOuterMassPrefixMasses_succ,
    parisiOuterMassPrefixVars_succ]
  rw [integral_cascadeTiltMeasure_gaussian_snoc
    (parisiMassPrefixMasses ms r) (parisiMassPrefixVars ξ qs r)
    (fun p => hm.2.1 _) (fun p => (hm.2.2 _).le) hA.continuous.measurable
    (abs_parisiQSuffix_sub_le ξ 0 ms qs r.castSucc) (hm.2.1 r) (hm.2.2 r).le
    (parisiVar ξ qs (r.val + 1)) (hz.1 + hz.2) hFm hFb]
  rw [hvL]
  simp only [coleHopfIterateSplitSpatialMoment, coleHopfSplitSpatialMoment_zero_eq]

/-- The initial outer moment at the first overlap is the corresponding
root moment, with the field/root Fubini argument justified by bounded spatial
derivatives rather than extra external-field moments. -/
theorem parisiLeftUSpatialMoment_first_zero_eq_parisiRootUSpatialMoment
    (s : ℕ) (hs : s ∈ Finset.Icc 1 4) {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    parisiLeftUSpatialMoment s μh ξ ms qs 0 0 = parisiRootUSpatialMoment s μh ξ ms qs 0 := by
  have hv : (deriv ξ (qExt qs 2) - deriv ξ (qs 0)).toNNReal = parisiVar ξ qs 1 := by
    unfold parisiVar
    rw [qExt_succ_of_lt qs (show 0 < k + 1 by omega)]
    rfl
  have hv₀ : parisiVar ξ qs 0 = (deriv ξ (qs 0) - deriv ξ 0).toNNReal := by
    simp [parisiVar, qExt_succ_of_lt]
  obtain ⟨hA, C, hC⟩ := parisiRootSuffix_spatial_regular_four ξ ms qs
  have hsc : (s : WithTop ℕ∞) ≤ 4 := by exact_mod_cast (Finset.mem_Icc.1 hs).2
  have hFm := (hA.continuous_iteratedDeriv s hsc).measurable.pow_const 2
  have hint : Integrable (fun hz : ℝ × ℝ =>
      (iteratedDeriv s (parisiRootSuffix ξ ms qs) (hz.1 + hz.2)) ^ 2)
      (μh.prod (gaussianReal 0 (parisiVar ξ qs 0))) := by
    refine Integrable.of_bound (hFm.comp (measurable_fst.add measurable_snd)).aestronglyMeasurable
      (C ^ 2) (.of_forall fun hz => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC s hs _) 2
  have hpoint (x : ℝ) : coleHopfIterateOuterSplitSpatialMoment s
      (parisiOuterMassPrefixMasses ms (0 : Fin (k + 1)))
      (parisiOuterMassPrefixVars ξ qs (0 : Fin (k + 1))) (mExt ms 1)
      (deriv ξ (qExt qs 2) - deriv ξ (qs 0)) (parisiQSuffix ξ 0 ms qs 0) x 0 =
      (iteratedDeriv s (parisiRootSuffix ξ ms qs) x) ^ 2 := by
    rw [coleHopfIterateOuterSplitSpatialMoment_zero_eq, hv,
      ← parisiRootSuffix_eq_coleHopf_first]
    have hpm : parisiOuterMassPrefixMasses ms (0 : Fin (k + 1)) =
        (Fin.elim0 : Fin 0 → ℝ) := funext fun p => Fin.elim0 p
    have hpv : parisiOuterMassPrefixVars ξ qs (0 : Fin (k + 1)) =
        (Fin.elim0 : Fin 0 → ℝ≥0) := funext fun p => Fin.elim0 p
    rw [hpm, hpv]
    change (∫ zs : Fin 0 → ℝ,
      (iteratedDeriv s (parisiRootSuffix ξ ms qs) (x + ∑ p, zs p)) ^ 2
      ∂(Measure.pi (fun p : Fin 0 => gaussianReal 0 p.elim0)).withDensity 1) = _
    rw [withDensity_one]
    simp [Finset.univ_eq_empty]
  unfold parisiLeftUSpatialMoment
  change (∫ hz : ℝ × ℝ, coleHopfIterateOuterSplitSpatialMoment s
      (parisiOuterMassPrefixMasses ms (0 : Fin (k + 1)))
      (parisiOuterMassPrefixVars ξ qs (0 : Fin (k + 1))) (mExt ms 1)
      (deriv ξ (qExt qs 2) - deriv ξ (qs 0)) (parisiQSuffix ξ 0 ms qs 0)
      (hz.1 + hz.2) 0 ∂μh.prod (gaussianReal 0 (parisiVar ξ qs 0))) = _
  simp_rw [hpoint]
  rw [integral_prod _ hint]
  unfold parisiRootUSpatialMoment
  simp only [coleHopfSplitSpatialMoment_zero_eq, coleHopfQ_zero, mul_one, hv₀]

/-- The initial outer U' moment is exactly the old random-field q-moment
at every free overlap, including the terminal index and k=0. -/
theorem parisiLeftUSpatialMoment_one_zero_eq_randomFieldParisiQMoment
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) :
    parisiLeftUSpatialMoment 1 μh ξ ms qs p 0 = randomFieldParisiQMoment μh ξ ms qs p := by
  refine Fin.cases ?_ (fun r => ?_) p
  · rw [parisiLeftUSpatialMoment_first_zero_eq_parisiRootUSpatialMoment 1 (by decide),
      parisiRootUSpatialMoment_one_zero_eq_randomFieldParisiQMoment μh ξ ms qs hm]
  · rw [parisiLeftUSpatialMoment_succ_zero_eq_parisiRightUSpatialMoment 1 (by decide)
      μh ξ ms qs r hm,
      parisiRightUSpatialMoment_one_zero_eq_randomFieldParisiQMoment hξ ms qs r hm hq]

/-- Proposition 14.7.5 supplies a strictly positive interval for every
outer split of the q-minimizer, including its terminal interval. -/
theorem parisi_outer_overlap_gap_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    qs p < qExt qs (p.val + 2) := by
  have hg := (randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
    ms qs hm hξ hμ hmin).1 (p.val + 1) (by omega)
  simpa only [qExt_succ_of_lt qs p.isLt] using hg

/-- Mirror U'(0)=q_L follows from the actual spatial moment and law-level
q-stationarity. The derivative is within the admissible variance interval. -/
theorem hasDerivWithinAt_parisiLeftU_zero_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    HasDerivWithinAt (parisiLeftU μh ξ ms qs p) (qs p)
      (Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) 0 := by
  have hgap := parisi_outer_overlap_gap_of_isMin ms qs p hm hξ hμ hmin
  have ha : 0 < deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) := sub_pos.2
    (hξ.strictMonoOn_deriv (hmin.1.mem_Icc p)
      (qExt_mem_Icc hmin.1.monotone hmin.1.2.1 hmin.1.2.2 _) hgap)
  have hd := hasDerivWithinAt_parisiLeftU (μh := μh) hξ ms qs p hm hmin.1 hgap
    (w := 0) ⟨le_rfl, ha.le⟩
  rw [parisiLeftUSpatialMoment_one_zero_eq_randomFieldParisiQMoment hξ ms qs p hm hmin.1,
    ← (randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
      ms qs hm hξ hμ hmin).2 p] at hd
  exact hd

/-- The mirror f is stationary at its left overlap endpoint, using the
admissible one-sided derivative and no assumed endpoint moments. -/
theorem hasDerivWithinAt_parisiLeftf_left_endpoint_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    HasDerivWithinAt (parisiLeftf μh ξ ms qs p) 0
      (Icc (qs p) (qExt qs (p.val + 2))) (qs p) := by
  have hgap := parisi_outer_overlap_gap_of_isMin ms qs p hm hξ hμ hmin
  have hd := hasDerivWithinAt_parisiLeftf (μh := μh) hξ ms qs p hm hmin.1 hgap
    (u := qs p) ⟨le_rfl, hgap.le⟩
  simpa only [sub_self, parisiLeftUSpatialMoment_one_zero_eq_randomFieldParisiQMoment
    hξ ms qs p hm hmin.1,
    ← (randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
      ms qs hm hξ hμ hmin).2 p, mul_zero] using hd

/-- Derivative form of the mirror U'(0)=q_L. -/
theorem derivWithin_parisiLeftU_zero_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    derivWithin (parisiLeftU μh ξ ms qs p)
      (Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) 0 = qs p := by
  have hgap := parisi_outer_overlap_gap_of_isMin ms qs p hm hξ hμ hmin
  have ha : 0 < deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) := sub_pos.2
    (hξ.strictMonoOn_deriv (hmin.1.mem_Icc p)
      (qExt_mem_Icc hmin.1.monotone hmin.1.2.1 hmin.1.2.2 _) hgap)
  exact (hasDerivWithinAt_parisiLeftU_zero_of_isMin ms qs p hm hξ hμ hmin).derivWithin
    (uniqueDiffOn_Icc ha 0 ⟨le_rfl, ha.le⟩)

/-- Derivative form of mirror stationarity at the left overlap. -/
theorem derivWithin_parisiLeftf_left_endpoint_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    derivWithin (parisiLeftf μh ξ ms qs p)
      (Icc (qs p) (qExt qs (p.val + 2))) (qs p) = 0 := by
  have hgap := parisi_outer_overlap_gap_of_isMin ms qs p hm hξ hμ hmin
  exact (hasDerivWithinAt_parisiLeftf_left_endpoint_of_isMin ms qs p hm hξ hμ hmin).derivWithin
    (uniqueDiffOn_Icc hgap (qs p) ⟨le_rfl, hgap.le⟩)

/-- At a nonterminal right endpoint, the empty inner interval leaves
the original mass coordinate as the freely varied outer mass. -/
theorem closedParisiX₀_split_left_right_endpoint_eq_mass_update
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (p : Fin k) (m h : ℝ) :
    closedParisiX₀ ξ (splitParisiMassLeft ms p.castSucc m)
        (splitParisiOverlap qs p.castSucc (qs p.succ)) h =
      closedParisiX₀ ξ (Function.update ms p m) qs h := by
  have hpm : parisiOuterMassPrefixMasses ms p.castSucc = parisiMassPrefixMasses ms p := by
    funext r
    exact mExt_val_succ ms (⟨r.val, by omega⟩ : Fin k)
  have hpv : parisiOuterMassPrefixVars ξ qs p.castSucc = parisiMassPrefixVars ξ qs p := rfl
  have hqR : qExt qs (p.castSucc.val + 2) = qs p.succ :=
    qExt_succ_of_lt qs p.succ.isLt
  have hv : parisiVar ξ qs (p.val + 1) =
      (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)).toNNReal := by
    unfold parisiVar
    change (deriv ξ (qExt qs (p.succ.val + 1)) -
      deriv ξ (qExt qs (p.castSucc.val + 1))).toNNReal = _
    rw [qExt_succ_of_lt qs p.succ.isLt, qExt_succ_of_lt qs p.castSucc.isLt]
  have hz : coleHopf (mExt ms (p.castSucc.val + 1)) (0 : ℝ≥0)
      (parisiQSuffix ξ 0 ms qs p.castSucc) = parisiQSuffix ξ 0 ms qs p.castSucc :=
    funext fun x => coleHopf_zero_var _ _ x
  rw [closedParisiX₀_split_left_eq, closedParisiX₀_mass_update_eq, hpm, hpv, hqR, hv]
  simp only [sub_self, Real.toNNReal_zero, hz]
  rfl

/-- Interior mass stationarity gives the mirror f right endpoint at every
nonterminal mass coordinate. The terminal fixed mass one is excluded. -/
theorem parisiLeftf_right_endpoint_eq_zero_of_isMinOn
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hmin : IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain k) (ms, qs)) :
    parisiLeftf μh ξ ms qs p.castSucc (qs p.succ) = 0 := by
  have hmp : ms p ∈ Icc (0 : ℝ) 1 := ⟨(hm.2.1 p).le, (hm.2.2 p).le⟩
  have hold := hasDerivWithinAt_randomFieldParisiX₀_mass_update hμ ξ ms qs p
    (fun r => hm.2.1 _) (fun r => (hm.2.2 _).le) hmp
  have hqR : qExt qs (p.castSucc.val + 2) = qs p.succ :=
    qExt_succ_of_lt qs p.succ.isLt
  have hnew := hasDerivAt_integral_closedParisiX₀_split_left_mass hμ hξ ms qs p.castSucc hm hq
    (u := qs p.succ) ⟨hq.monotone (by change p.val ≤ p.val + 1; omega), hqR.symm.le⟩
  have he : (fun b => ∫ h, closedParisiX₀ ξ (splitParisiMassLeft ms p.castSucc b)
      (splitParisiOverlap qs p.castSucc (qs p.succ)) h ∂μh) =
      fun b => ∫ h, closedParisiX₀ ξ (Function.update ms p b) qs h ∂μh := by
    funext b
    exact integral_congr_ae (.of_forall fun h =>
      closedParisiX₀_split_left_right_endpoint_eq_mass_update ξ ms qs p b h)
  rw [he] at hnew
  simp only [Fin.val_castSucc, mExt_val_succ ms p] at hnew
  have hM := (hold.derivWithin (uniqueDiffOn_Icc_zero_one _ hmp)).symm.trans
    (hnew.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one _ hmp))
  have hqmem : qs ∈ parisiOverlapDomain k :=
    mem_parisiOverlapDomain_iff.2 ⟨hq.monotone, hq.2.1, hq.2.2⟩
  have hstat := randomFieldParisiMassMoment_sub_theta_eq_zero_of_isMinOn hμ ξ ms qs p hm hqmem hmin
  have hqL : qExt qs (p.val + 1) = qs p.castSucc := qExt_succ_of_lt qs p.castSucc.isLt
  rw [hM, hqL, show p.val + 2 = p.castSucc.val + 2 by rfl, hqR] at hstat
  unfold parisiLeftf
  linarith

end SpinGlass
