import SpinGlass.Parisi.Variational.ParisiSpatialThird
import SpinGlass.Parisi.Variational.ParisiOuterSplitResponse

/-!
# Uniform spatial moments in the overlap response

The sharp spatial invariant bounds the actual first two squared moments
between zero and one. These bounds survive the baseline prefix and the
external-field/root product average. All constants are independent of the
MIN, the number of levels and the field law, as required by (14.240)-(14.247).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- The actual post-root suffix satisfies the sharp spatial invariant. -/
theorem parisiRootSuffix_sharp_spatial_bounds (ξ : ℝ → ℝ) {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (x : ℝ) :
    0 ≤ deriv (deriv (parisiRootSuffix ξ ms qs)) x ∧
      deriv (deriv (parisiRootSuffix ξ ms qs)) x + deriv (parisiRootSuffix ξ ms qs) x ^ 2 ≤ 1 := by
  obtain ⟨C, hC⟩ := exists_bound_iteratedDeriv_parisiLogCoshTerminal_four 0
  apply coleHopfIterate_sharp_spatial_bounds (contDiff_parisiLogCoshTerminal 0 4) hC
    (parisiLogCoshTerminal_sharp_spatial_bounds 0)
  intro p
  rw [parisiLevelMasses_apply]
  exact ⟨(hm.mExt_pos (by omega)).le, mExt_le_one (fun r => (hm.2.2 r).le) _⟩

/-- The local squared-gradient and squared-curvature moments have the
uniform envelope one, including zero matching mass and either zero variance. -/
theorem coleHopfSplitSpatialMoment_mem_Icc_of_sharp {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ i ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv i A x| ≤ C)
    (hsharp : ∀ x, 0 ≤ deriv (deriv A) x ∧ deriv (deriv A) x + deriv A x ^ 2 ≤ 1)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) {i : ℕ} (hi : i ∈ Finset.Icc 1 2)
    (a v x : ℝ) : coleHopfSplitSpatialMoment i m a A x v ∈ Icc (0 : ℝ) 1 := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hBL := abs_coleHopf_sub_le_of_lipschitz m hA.continuous.measurable hL v.toNNReal
  have hBc := (lipschitzWith_toNNReal_of_abs_sub_le hBL).continuous
  have hBg := HasLinearGrowth.of_lipschitz hBL
  have hB4 := contDiff_four_coleHopf hA hb m v.toNNReal
  have hbound : ∀ y, |iteratedDeriv i (coleHopf m v.toNNReal A) y| ≤ 1 := by
    intro y
    have hs := coleHopf_sharp_spatial_bounds (hA.of_le (by norm_num)) hsharp hm v.toNNReal y
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
    interval_cases i
    · rw [iteratedDeriv_one]
      apply abs_le.2
      constructor <;> nlinarith [hs.1, hs.2]
    · simp only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
      rw [abs_of_nonneg hs.1]
      nlinarith [hs.2, sq_nonneg (deriv (coleHopf m v.toNNReal A) y)]
  have hupper : |coleHopfSplitSpatialMoment i m a A x v| ≤ 1 := by
    apply abs_integral_mul_coleHopfQ_le' hBg hBc.measurable m
      ((hB4.continuous_iteratedDeriv i (by
        exact_mod_cast (show i ≤ 4 by have hh := (Finset.mem_Icc.1 hi).2; omega))).pow 2).measurable
    intro y
    rw [Pi.pow_apply, abs_pow]
    simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hbound y) 2
  exact ⟨coleHopfSplitSpatialMoment_nonneg _ _ _ _ _ _, (le_abs_self _).trans hupper⟩

/-- Fixed-prefix averaging preserves the sharp moment envelope. -/
theorem coleHopfIterateSplitSpatialMoment_mem_Icc_of_sharp {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ i ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv i A x| ≤ C)
    (hsharp : ∀ x, 0 ≤ deriv (deriv A) x ∧ deriv (deriv A) x + deriv A x ^ 2 ≤ 1)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) {i : ℕ} (hi : i ∈ Finset.Icc 1 2)
    (a v x : ℝ) : coleHopfIterateSplitSpatialMoment i ms vs m a A x v ∈ Icc (0 : ℝ) 1 := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hBL := abs_coleHopf_sub_le_of_lipschitz m hA.continuous.measurable hL a.toNNReal
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hBL).continuous.measurable
  have hbnd : ∀ y, |coleHopfSplitSpatialMoment i m a A y v| ≤ 1 := fun y =>
    abs_le.2 ⟨by linarith [(coleHopfSplitSpatialMoment_mem_Icc_of_sharp
      hA hb hsharp hLip hm hi a v y).1],
      (coleHopfSplitSpatialMoment_mem_Icc_of_sharp hA hb hsharp hLip hm hi a v y).2⟩
  have hu := abs_integral_cascadeTiltMeasure_le ms vs hpos hle hBm hBL x hbnd
  refine ⟨integral_nonneg (fun zs => coleHopfSplitSpatialMoment_nonneg _ _ _ _ _ _), ?_⟩
  exact (le_abs_self _).trans hu

/-- Root moments are bounded independently of the external field law and
all parameters. No field moment assumption is needed for this bounded input. -/
theorem parisiRootUSpatialMoment_mem_Icc
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 2) (v : ℝ) :
    parisiRootUSpatialMoment i μh ξ ms qs v ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hA, C, hC⟩ := parisiRootSuffix_spatial_regular_four ξ ms qs
  have hbnd := fun h => coleHopfSplitSpatialMoment_mem_Icc_of_sharp hA hC
    (parisiRootSuffix_sharp_spatial_bounds ξ qs hm) (abs_parisiRootSuffix_sub_le ξ ms qs)
    (m := 0) ⟨le_rfl, zero_le_one⟩ hi (deriv ξ (qs 0) - deriv ξ 0) v h
  have hh := norm_integral_le_of_norm_le_const (μ := μh)
    (f := fun h => coleHopfSplitSpatialMoment i 0 (deriv ξ (qs 0) - deriv ξ 0)
      (parisiRootSuffix ξ ms qs) h v)
    (.of_forall fun h => by rw [Real.norm_eq_abs, abs_of_nonneg (hbnd h).1]; exact (hbnd h).2)
  refine ⟨parisiRootUSpatialMoment_nonneg i μh ξ ms qs v, ?_⟩
  exact (le_abs_self _).trans (by
    simpa only [parisiRootUSpatialMoment, Real.norm_eq_abs, probReal_univ, mul_one] using hh)

/-- The nonroot moment envelope includes the fixed cascade prefix and
the independent field/root Gaussian product average. -/
theorem parisiRightUSpatialMoment_mem_Icc
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (hm : ParisiMAdmissible ms)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 2) (v : ℝ) :
    parisiRightUSpatialMoment i μh ξ ms qs p v ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hA, C, hC⟩ := parisiQSuffix_spatial_regular_four ξ 0 ms qs p.castSucc
  have hbnd := fun y => coleHopfIterateSplitSpatialMoment_mem_Icc_of_sharp
    (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p)
    (fun r => hm.2.1 _) (fun r => (hm.2.2 _).le) hA hC
    (parisiQSuffix_sharp_spatial_bounds ξ 0 qs p.castSucc hm)
    (abs_parisiQSuffix_sub_le ξ 0 ms qs p.castSucc)
    ⟨(hm.2.1 p).le, (hm.2.2 p).le⟩ hi
    (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)) v y
  have hh := norm_integral_le_of_norm_le_const
    (μ := μh.prod (gaussianReal 0 (parisiVar ξ qs 0)))
    (f := fun hz : ℝ × ℝ => coleHopfIterateSplitSpatialMoment i
      (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p) (ms p)
      (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))
      (parisiQSuffix ξ 0 ms qs p.castSucc) (hz.1 + hz.2) v)
    (.of_forall fun hz => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbnd (hz.1 + hz.2)).1]
      exact (hbnd (hz.1 + hz.2)).2)
  refine ⟨integral_nonneg (fun hz => (hbnd (hz.1 + hz.2)).1), ?_⟩
  exact (le_abs_self _).trans (by
    simpa only [parisiRightUSpatialMoment, Real.norm_eq_abs, probReal_univ, mul_one] using hh)

/-- The root gradient moment is uniformly Lipschitz in the admissible
variance coordinate, including both one-sided endpoints. -/
theorem abs_parisiRootUSpatialMoment_one_sub_le
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (ha : 0 < deriv ξ (qs 0) - deriv ξ 0) {v w : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0))
    (hw : w ∈ Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) :
    |parisiRootUSpatialMoment 1 μh ξ ms qs w - parisiRootUSpatialMoment 1 μh ξ ms qs v| ≤
      |w - v| := by
  have hh :=
    (convex_Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => hasDerivWithinAt_parisiRootUSpatialMoment_one (μh := μh) ξ ms qs ha ht)
      (fun t _ => by
        rw [Real.norm_eq_abs, abs_neg]
        have hbnd := parisiRootUSpatialMoment_mem_Icc (μh := μh) ξ ms qs hm (i := 2) (by decide) t
        exact abs_le.2 ⟨by linarith [hbnd.1], hbnd.2⟩) hv hw
  simpa only [Real.norm_eq_abs, one_mul] using hh

/-- The nonroot gradient moment is uniformly Lipschitz after all preceding
averages, with no dependence on the number of prefix levels. -/
theorem abs_parisiRightUSpatialMoment_one_sub_le
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {v w : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)))
    (hw : w ∈ Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) :
    |parisiRightUSpatialMoment 1 μh ξ ms qs p w - parisiRightUSpatialMoment 1 μh ξ ms qs p v| ≤
      |w - v| := by
  have hconv : Convex ℝ (Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) :=
    convex_Icc _ _
  have hh := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => hasDerivWithinAt_parisiRightUSpatialMoment_one (μh := μh) hξ ms qs p hm hq ht)
      (fun t _ => by
        rw [Real.norm_eq_abs, abs_neg]
        have hbnd := parisiRightUSpatialMoment_mem_Icc (μh := μh) ξ ms qs p hm
          (i := 2) (by decide) t
        exact abs_le.2 ⟨by linarith [hbnd.1], hbnd.2⟩) hv hw
  simpa only [Real.norm_eq_abs, one_mul] using hh

/-- Uniform derivative bounds for the actual root response in (14.240).
The slope and curvature are identified with the bounded concrete moments. -/
theorem parisiRootU_derivWithin_bounds
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (ha : 0 < deriv ξ (qs 0) - deriv ξ 0) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) :
    derivWithin (parisiRootU μh ξ ms qs) (Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) v ∈
      Icc (0 : ℝ) 1 ∧
    derivWithin (parisiRootUSpatialMoment 1 μh ξ ms qs)
      (Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) v ∈ Icc (-1 : ℝ) 0 := by
  rw [(hasDerivWithinAt_parisiRootU ξ ms qs ha hv).derivWithin (uniqueDiffOn_Icc ha v hv),
    (hasDerivWithinAt_parisiRootUSpatialMoment_one ξ ms qs ha hv).derivWithin
      (uniqueDiffOn_Icc ha v hv)]
  have hbnd := parisiRootUSpatialMoment_mem_Icc (μh := μh) ξ ms qs hm (i := 2) (by decide) v
  exact ⟨parisiRootUSpatialMoment_mem_Icc ξ ms qs hm (by decide) v,
    ⟨by linarith [hbnd.2], by linarith [hbnd.1]⟩⟩

/-- Uniform derivative bounds for the actual nonroot response, retaining
the fixed prefix and the i.i.d. field/root averaging. -/
theorem parisiRightU_derivWithin_bounds
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) :
    derivWithin (parisiRightU μh ξ ms qs p)
      (Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) v ∈ Icc (0 : ℝ) 1 ∧
    derivWithin (parisiRightUSpatialMoment 1 μh ξ ms qs p)
      (Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) v ∈ Icc (-1 : ℝ) 0 := by
  have ha : 0 < deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) := sub_pos.2
    (hξ.strictMonoOn_deriv (hq.mem_Icc p.castSucc) (hq.mem_Icc p.succ)
      (hq.1 (by change p.val < p.val + 1; omega)))
  rw [(hasDerivWithinAt_parisiRightU hξ ms qs p hm hq hv).derivWithin
      (uniqueDiffOn_Icc ha v hv),
    (hasDerivWithinAt_parisiRightUSpatialMoment_one hξ ms qs p hm hq hv).derivWithin
      (uniqueDiffOn_Icc ha v hv)]
  have hbnd := parisiRightUSpatialMoment_mem_Icc (μh := μh) ξ ms qs p hm (i := 2) (by decide) v
  exact ⟨parisiRightUSpatialMoment_mem_Icc ξ ms qs p hm (by decide) v,
    ⟨by linarith [hbnd.2], by linarith [hbnd.1]⟩⟩

/-- The complete post-root spatial recursion and an additional lower-mass
layer share the uniform third derivative constant twelve. -/
theorem coleHopf_parisiRootSuffix_third_spatial_bound (ξ : ℝ → ℝ) {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 ≤ m) (hmr : m ≤ mExt ms 1) (v : ℝ≥0) (x : ℝ) :
    |iteratedDeriv 3 (coleHopf m v (parisiRootSuffix ξ ms qs)) x| ≤ 12 := by
  apply coleHopf_ordered_logCoshIterate_third_spatial_bound
    (parisiLevelMasses ms) (parisiLevelVars ξ qs)
    (fun p q hpq => by
      simp only [parisiLevelMasses_apply]
      exact hm.monotone_mExt (by change p.val + 1 ≤ q.val + 1; omega))
    (fun p => by rw [parisiLevelMasses_apply]; exact hm.mExt_pos (by omega))
    (fun p => by rw [parisiLevelMasses_apply]; exact mExt_le_one (fun s => (hm.2.2 s).le) _)
    ⟨hm0, hmr.trans (mExt_le_one (fun s => (hm.2.2 s).le) _)⟩
  intro p
  rw [parisiLevelMasses_apply]
  exact hmr.trans (hm.monotone_mExt (by omega))

/-- Both outer spatial moments lie between zero and one after the fixed
prefix and independent field/root averages, including the terminal split. -/
theorem parisiLeftUSpatialMoment_mem_Icc
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) {i : ℕ} (hi : i ∈ Finset.Icc 1 2) (w : ℝ) :
    parisiLeftUSpatialMoment i μh ξ ms qs p w ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hA, C, hC⟩ := parisiQSuffix_spatial_regular_four ξ 0 ms qs p
  let a := deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p)
  have hbnd := fun y => coleHopfIterateSplitSpatialMoment_mem_Icc_of_sharp
    (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
    (fun r => hm.mExt_pos (by omega))
    (fun r => mExt_le_one (fun s => (hm.2.2 s).le) _) hA hC
    (parisiQSuffix_sharp_spatial_bounds ξ 0 qs p hm)
    (abs_parisiQSuffix_sub_le ξ 0 ms qs p)
    ⟨(hm.mExt_pos (by omega : 0 < p.val + 1)).le,
      mExt_le_one (fun s => (hm.2.2 s).le) _⟩ hi a (a - w) y
  unfold parisiLeftUSpatialMoment coleHopfIterateOuterSplitSpatialMoment
  have hh := norm_integral_le_of_norm_le_const
    (μ := μh.prod (gaussianReal 0 (parisiVar ξ qs 0)))
    (f := fun hz : ℝ × ℝ => coleHopfIterateSplitSpatialMoment i
      (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
      (mExt ms (p.val + 1)) a (parisiQSuffix ξ 0 ms qs p) (hz.1 + hz.2) (a - w))
    (.of_forall fun hz => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbnd (hz.1 + hz.2)).1]
      exact (hbnd (hz.1 + hz.2)).2)
  refine ⟨integral_nonneg (fun hz => (hbnd (hz.1 + hz.2)).1), ?_⟩
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hh)

end SpinGlass
