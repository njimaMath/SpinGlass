import SpinGlass.Parisi.Variational.ParisiSpatialBounds
import SpinGlass.Parisi.Variational.ParisiSplitResponse

/-!
# Uniform first-overlap separation

Talagrand, Vol. II, (14.270) is derived from the actual root recursion,
the lower-curvature propagation (14.274), Gaussian Jensen and the concrete
q-stationarity theorem. The constant is chosen before the MIN parameters.
Only a probability field law with finite positive second moment is required.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- The complete zero-field spatial recursion, including the root Gaussian. -/
noncomputable def parisiRootSpatialFunction (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) : ℝ → ℝ :=
  coleHopf 0 (parisiVar ξ qs 0) (parisiRootSuffix ξ ms qs)

/-- The complete spatial recursion is an actual iterate with root mass zero. -/
theorem parisiRootSpatialFunction_eq_iterate (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    parisiRootSpatialFunction ξ ms qs = coleHopfIterate (k + 2)
      (Fin.cons 0 (parisiLevelMasses ms))
      (Fin.cons (parisiVar ξ qs 0) (parisiLevelVars ξ qs)) (parisiLogCoshTerminal 0) := by
  rw [coleHopfIterate_succ]
  rfl

private lemma root_masses_mem_Icc {k : ℕ} {ms : Fin k → ℝ}
    (hm : ParisiMAdmissible ms) :
    ∀ p : Fin (k + 2), Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms) p ∈
      Icc (0 : ℝ) 1 := by
  intro p
  refine Fin.cases (by simp) (fun i => ?_) p
  simp only [Fin.cons_succ, parisiLevelMasses_apply]
  exact ⟨(hm.mExt_pos (by omega)).le, mExt_le_one (fun i => (hm.2.2 i).le) _⟩

/-- Telescoping of all actual variances, including the root and last layer.
Clamping is discharged from the book hypotheses and the closed overlap domain. -/
theorem sum_parisiVar_of_talagrand {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (hq : qs ∈ parisiOverlapDomain k) :
    ∑ p : Fin (k + 2), (parisiVar ξ qs p.val : ℝ) = deriv ξ 1 - deriv ξ 0 := by
  obtain ⟨hmono, hq0, hq1⟩ := mem_parisiOverlapDomain_iff.1 hq
  have hvar : ∀ n < k + 2, (parisiVar ξ qs n : ℝ) =
      deriv ξ (qExt qs (n + 1)) - deriv ξ (qExt qs n) := by
    intro n hn
    unfold parisiVar
    apply Real.coe_toNNReal
    exact sub_nonneg.2 (hξ.strictMonoOn_deriv.monotoneOn
      (qExt_mem_Icc hmono hq0 hq1 n) (qExt_mem_Icc hmono hq0 hq1 (n + 1))
      (qExt_le_succ hmono hq0 hq1 (by omega)))
  rw [Fin.sum_univ_eq_sum_range (fun n => (parisiVar ξ qs n : ℝ)) (k + 2)]
  rw [Finset.sum_congr rfl (fun n hn => hvar n (Finset.mem_range.1 hn)),
    Finset.sum_range_sub (fun n => deriv ξ (qExt qs n)), qExt_zero, qExt_of_le qs le_rfl]

/-- The root function has fourth-order spatial regularity with bounded
derivatives. The auxiliary bound is used for regularity only. -/
theorem parisiRootSpatialFunction_spatial_regular_four (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    ContDiff ℝ 4 (parisiRootSpatialFunction ξ ms qs) ∧
      ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ x,
        |iteratedDeriv j (parisiRootSpatialFunction ξ ms qs) x| ≤ C := by
  rw [parisiRootSpatialFunction_eq_iterate]
  exact coleHopfIterate_spatial_regular_four _ _ (contDiff_parisiLogCoshTerminal 0 4)
    (exists_bound_iteratedDeriv_parisiLogCoshTerminal_four 0)

/-- Sharp root-function bounds, independent of all admissible parameters. -/
theorem parisiRootSpatialFunction_sharp_spatial_bounds (ξ : ℝ → ℝ) {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (x : ℝ) :
    0 ≤ deriv (deriv (parisiRootSpatialFunction ξ ms qs)) x ∧
      deriv (deriv (parisiRootSpatialFunction ξ ms qs)) x +
        deriv (parisiRootSpatialFunction ξ ms qs) x ^ 2 ≤ 1 := by
  obtain ⟨C, hC⟩ := exists_bound_iteratedDeriv_parisiLogCoshTerminal_four 0
  rw [parisiRootSpatialFunction_eq_iterate]
  exact coleHopfIterate_sharp_spatial_bounds (contDiff_parisiLogCoshTerminal 0 4) hC
    (parisiLogCoshTerminal_sharp_spatial_bounds 0) _ _ (root_masses_mem_Icc hm) x

/-- Uniform lower curvature (14.274), including the root expectation.
Its coefficient depends only on the profile's total variance. -/
theorem parisiRootSpatialFunction_curvature_lower {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {k : ℕ} {ms : Fin k → ℝ}
    (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : qs ∈ parisiOverlapDomain k) (x : ℝ) :
    Real.exp (-2 * (deriv ξ 1 - deriv ξ 0)) / Real.cosh x ^ 2 ≤
      deriv (deriv (parisiRootSpatialFunction ξ ms qs)) x := by
  have h := coleHopfIterate_logCosh_curvature_lower
    (Fin.cons 0 (parisiLevelMasses ms))
    (Fin.cons (parisiVar ξ qs 0) (parisiLevelVars ξ qs)) (root_masses_mem_Icc hm) x
  have hvs : Fin.cons (parisiVar ξ qs 0) (parisiLevelVars ξ qs) =
      fun p : Fin (k + 2) => parisiVar ξ qs p.val := by
    funext p
    refine Fin.cases rfl (fun i => ?_) p
    rfl
  rw [hvs, sum_parisiVar_of_talagrand hξ qs hq] at h
  simpa only [parisiRootSpatialFunction_eq_iterate, hvs] using h

/-- Symmetry gives the exact zero derivative at the origin, without imposing
symmetry on the external field law. -/
theorem deriv_parisiRootSpatialFunction_zero (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    deriv (parisiRootSpatialFunction ξ ms qs) 0 = 0 := by
  have heven : Function.Even (parisiLogCoshTerminal 0) := fun x => by
    simp only [parisiLogCoshTerminal, zero_add, Real.cosh_neg]
  apply deriv_zero_of_even
  · rw [parisiRootSpatialFunction_eq_iterate]
    exact coleHopfIterate_even (L := 1)
      (contDiff_parisiLogCoshTerminal 0 4).continuous.measurable
      (fun x y => by simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0 x y)
      heven _ _
  · exact ((parisiRootSpatialFunction_spatial_regular_four ξ ms qs).1.differentiable
      (by norm_num)) 0

/-- The first concrete q-moment is the conditional Gaussian square of the
actual post-root derivative. This identifies the book moment with the recursion. -/
theorem parisiQMoment_first_eq_integral_root_deriv_sq (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (h : ℝ) :
    parisiQMoment ξ h ms qs 0 =
      ∫ z, deriv (parisiRootSuffix ξ ms qs) (h + z) ^ 2 ∂gaussianReal 0 (parisiVar ξ qs 0) := by
  rw [parisiQMoment_first_eq_root_spatial_moment ξ ms qs hm h]
  have hzero : coleHopf 0 (0 : ℝ≥0) (parisiRootSuffix ξ ms qs) =
      parisiRootSuffix ξ ms qs := funext fun x => coleHopf_zero_var 0 _ x
  simp only [coleHopfSplitSpatialMoment, Real.toNNReal_zero, hzero,
    iteratedDeriv_one, coleHopfQ_zero, mul_one, sub_zero]
  rfl

/-- Gaussian Jensen bounds the first q-moment below by the square of the
complete root derivative, for every realized site field. -/
theorem deriv_parisiRootSpatialFunction_sq_le_first_moment (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (h : ℝ) :
    deriv (parisiRootSpatialFunction ξ ms qs) h ^ 2 ≤ parisiQMoment ξ h ms qs 0 := by
  have hsharp : ∀ x, 0 ≤ deriv (deriv (parisiRootSuffix ξ ms qs)) x ∧
      deriv (deriv (parisiRootSuffix ξ ms qs)) x + deriv (parisiRootSuffix ξ ms qs) x ^ 2 ≤ 1 := by
    obtain ⟨C, hC⟩ := exists_bound_iteratedDeriv_parisiLogCoshTerminal_four 0
    apply coleHopfIterate_sharp_spatial_bounds (contDiff_parisiLogCoshTerminal 0 4) hC
      (parisiLogCoshTerminal_sharp_spatial_bounds 0)
    intro p
    rw [parisiLevelMasses_apply]
    exact ⟨(hm.mExt_pos (by omega)).le, mExt_le_one (fun i => (hm.2.2 i).le) _⟩
  have hfirst : ∀ x, |deriv (parisiRootSuffix ξ ms qs) x| ≤ 1 := fun x => by
    apply abs_le.2
    constructor <;> nlinarith [(hsharp x).1, (hsharp x).2]
  have hsecond : ∀ x, |deriv (deriv (parisiRootSuffix ξ ms qs)) x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hsharp x).1]
    nlinarith [(hsharp x).2, sq_nonneg (deriv (parisiRootSuffix ξ ms qs) x)]
  rw [parisiQMoment_first_eq_integral_root_deriv_sq ξ ms qs hm h]
  exact coleHopf_zero_spatial_deriv_sq_le_integral
    ((parisiRootSuffix_spatial_regular_four ξ ms qs).1.of_le (by norm_num))
    hfirst hsecond (parisiVar ξ qs 0) h

/-- An explicit bound for (14.270), independent of the chosen MIN.
It uses the field law only through its bounded positive tanh-square moment. -/
theorem parisiQ_first_ge_exp_mul_tanh_sq_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) (hμ : NondegenerateExternalFieldLaw μh)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    Real.exp (-4 * (deriv ξ 1 - deriv ξ 0)) * (∫ h, Real.tanh h ^ 2 ∂μh) ≤ qs 0 := by
  let A := parisiRootSpatialFunction ξ ms qs
  let c := Real.exp (-2 * (deriv ξ 1 - deriv ξ 0))
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hq : qs ∈ parisiOverlapDomain k := mem_parisiOverlapDomain_iff.2
    ⟨hmin.1.1.monotone, hmin.1.2.1, hmin.1.2.2⟩
  have hA : ContDiff ℝ 2 A :=
    (parisiRootSpatialFunction_spatial_regular_four ξ ms qs).1.of_le (by norm_num)
  have hA₁ : ContDiff ℝ 1 (deriv A) := (contDiff_succ_iff_deriv.1 hA).2.2
  have hsharp := parisiRootSpatialFunction_sharp_spatial_bounds ξ qs hm
  have hfirst : ∀ h, |deriv A h| ≤ 1 := fun h => by
    apply abs_le.2
    constructor <;> nlinarith [(hsharp h).1, (hsharp h).2]
  have hD : Integrable (fun h => deriv A h ^ 2) μh :=
    Integrable.of_bound (hA₁.continuous.measurable.pow_const 2).aestronglyMeasurable 1
      (.of_forall fun h => by
        rw [Real.norm_eq_abs, abs_pow]
        nlinarith [hfirst h, abs_nonneg (deriv A h)])
  have hbound : ∀ h, c * |Real.tanh h| ≤ |deriv A h| :=
    Aristotle.abs_deriv_ge_mul_tanh hc (deriv_parisiRootSpatialFunction_zero ξ ms qs)
      (hA₁.differentiable one_ne_zero) (parisiRootSpatialFunction_curvature_lower hξ qs hm hq)
  have hlow := Aristotle.integral_sq_ge_tanh_sq hc hD (.of_forall hbound)
  have hmoment : Integrable (fun h => parisiQMoment ξ h ms qs 0) μh :=
    integrable_parisiQMoment_externalField qs 0 hm
  have hJ := integral_mono hD hmoment
    (deriv_parisiRootSpatialFunction_sq_le_first_moment ξ ms qs hm)
  have hstat := (randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
    ms qs hm hξ hμ hmin).2 0
  change qs 0 = ∫ h, parisiQMoment ξ h ms qs 0 ∂μh at hstat
  rw [← hstat] at hJ
  have hc_sq : c ^ 2 = Real.exp (-4 * (deriv ξ 1 - deriv ξ 0)) := by
    dsimp only [c]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hc_sq] at hlow
  exact hlow.trans hJ

/-- Uniform separation (14.270) is selected before the level count and MIN.
The coefficient depends only on ξ and the nondegenerate probability field law. -/
theorem exists_uniform_parisiQ_first_lower_bound
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) (hμ : NondegenerateExternalFieldLaw μh) :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs → c ≤ qs 0 := by
  refine ⟨Real.exp (-4 * (deriv ξ 1 - deriv ξ 0)) * (∫ h, Real.tanh h ^ 2 ∂μh),
    mul_pos (Real.exp_pos _)
      (Aristotle.integral_tanh_sq_pos hμ.sq_integrable hμ.second_moment_pos),
    fun k ms qs hm hmin => parisiQ_first_ge_exp_mul_tanh_sq_of_isMin hξ hμ ms qs hm hmin⟩

end SpinGlass
