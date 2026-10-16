import SpinGlass.Parisi.Coupled.CoupledGaussianPairLaw
import SpinGlass.Parisi.Coupled.CoupledRootNonnegative

/-!
# The signed initial-root response

The common/antisymmetric Gaussian moment is compared to the concrete
nonnegative root moment. The covariance bound uses the actual squared
curvature of the Parisi suffix under the external-field/root law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open Aristotle.Heat

/-- The fixed-variance Gaussian gradient correlation equals the actual
zero-mass split moment whenever its covariance is nonnegative. -/
theorem gaussianFixedVarianceCorrelation_eq_coleHopfSplitSpatialMoment_one
    {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C)
    {a v : ℝ} (hv : v ∈ Icc (0 : ℝ) a) (x : ℝ) :
    gaussianFixedVarianceCorrelation a (v / 2) (deriv A) x =
      coleHopfSplitSpatialMoment 1 0 a A x v := by
  have hfirst : ∀ y, |deriv A y| ≤ C := by
    simpa only [iteratedDeriv_one] using hb 1 (by decide)
  have hsecond : ∀ y, |deriv (deriv A) y| ≤ C := by
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
      iteratedDeriv_zero] using
      hb 2 (by decide)
  have hd (y : ℝ) : deriv (coleHopf 0 v.toNNReal A) y = heat v (deriv A) y := by
    simpa only [coleHopfQ_zero, mul_one, heat] using
      ((coleHopf_spatial_derivative_formulas (hA.of_le (by norm_num)) hfirst hsecond
        0 v.toNNReal).1 y).deriv
  have hh := gaussianFixedVarianceCorrelation_eq_square_heat
    (hA.continuous_deriv (by norm_num)) hfirst (a - v).toNNReal v.toNNReal x
  have hp : ((a - v).toNNReal : ℝ) = a - v := Real.coe_toNNReal _ (sub_nonneg.2 hv.2)
  have hq : (v.toNNReal : ℝ) = v := Real.coe_toNNReal _ hv.1
  rw [hp, hq, sub_add_cancel] at hh
  rw [hh]
  unfold coleHopfSplitSpatialMoment
  simp only [iteratedDeriv_one, coleHopfQ_zero, mul_one]
  simp_rw [hd]
  rfl

/-- The root Gaussian gradient correlation on the canonical signed
covariance, with both coordinate variances equal to the original root variance. -/
noncomputable def parisiRootSignedMoment (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u : ℝ) : ℝ :=
  let a := deriv ξ (qs 0) - deriv ξ 0
  ∫ h, gaussianFixedVarianceCorrelation a
    (t * (a + (deriv ξ |u| - deriv ξ 0)) / 2) (deriv (parisiRootSuffix ξ ms qs)) h ∂μh

noncomputable def parisiRootSignedResponseGap (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u : ℝ) : ℝ :=
  parisiRootSignedMoment μh ξ ms qs t u - u

/-- At zero overlap the signed covariance reduces to the actual
nonnegative root split moment, with the same external-field average. -/
theorem parisiRootSignedMoment_zero {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiRootSignedMoment μh ξ ms qs t 0 =
      parisiRootUSpatialMoment 1 μh ξ ms qs (t * (deriv ξ (qs 0) - deriv ξ 0)) := by
  obtain ⟨hA, C, hC⟩ := parisiRootSuffix_spatial_regular_four ξ ms qs
  have ha : 0 ≤ deriv ξ (qs 0) - deriv ξ 0 := sub_nonneg.2
    (hξ.strictMonoOn_deriv.monotoneOn ⟨le_rfl, zero_le_one⟩ (hq.mem_Icc 0) (hq.mem_Icc 0).1)
  have hv : t * (deriv ξ (qs 0) - deriv ξ 0) ∈ Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0) :=
    ⟨mul_nonneg ht.1 ha, by nlinarith [mul_le_mul_of_nonneg_right ht.2 ha]⟩
  unfold parisiRootSignedMoment parisiRootUSpatialMoment
  simp only [abs_zero, sub_self, add_zero]
  exact integral_congr_ae (.of_forall fun h =>
    gaussianFixedVarianceCorrelation_eq_coleHopfSplitSpatialMoment_one hA hC hv h)

/-- Covariance variation of the signed root moment is bounded by
the actual initial squared-curvature moment of the Parisi recursion. -/
theorem abs_parisiRootSignedMoment_sub_zero_le {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : |u| ≤ qs 0) :
    |parisiRootSignedMoment μh ξ ms qs t u - parisiRootSignedMoment μh ξ ms qs t 0| ≤
      t * (deriv ξ |u| - deriv ξ 0) * parisiRootUSpatialMoment 2 μh ξ ms qs 0 := by
  obtain ⟨hA, C, hC⟩ := parisiRootSuffix_spatial_regular_four ξ ms qs
  let a := deriv ξ (qs 0) - deriv ξ 0
  let b := deriv ξ |u| - deriv ξ 0
  have ha : 0 ≤ a := sub_nonneg.2
    (hξ.strictMonoOn_deriv.monotoneOn ⟨le_rfl, zero_le_one⟩ (hq.mem_Icc 0) (hq.mem_Icc 0).1)
  have humem : |u| ∈ Icc (0 : ℝ) 1 := ⟨abs_nonneg _, hu.trans (hq.mem_Icc 0).2⟩
  have hb : b ∈ Icc (0 : ℝ) a := ⟨sub_nonneg.2
    (hξ.strictMonoOn_deriv.monotoneOn ⟨le_rfl, zero_le_one⟩ humem (abs_nonneg _)),
    sub_le_sub_right (hξ.strictMonoOn_deriv.monotoneOn humem (hq.mem_Icc 0) hu) _⟩
  have hv : t * (a + b) / 2 ∈ Icc (0 : ℝ) a := by
    constructor
    · exact div_nonneg (mul_nonneg ht.1 (add_nonneg ha hb.1)) (by norm_num)
    · nlinarith [mul_le_mul_of_nonneg_left hb.2 ht.1,
        mul_le_mul_of_nonneg_right ht.2 ha]
  have hw : t * a / 2 ∈ Icc (0 : ℝ) a :=
    ⟨div_nonneg (mul_nonneg ht.1 ha) (by norm_num),
      by nlinarith [mul_le_mul_of_nonneg_right ht.2 ha]⟩
  have hJ := jet_iteratedDeriv hA hC
  have HH := abs_integral_gaussianFixedVarianceCorrelation_sub_le (μ := μh)
    (hJ.hasDeriv 1 (by omega)) (hJ.hasDeriv 2 (by omega))
    (hJ.continuous (by omega : 3 ≤ 4))
    (hC 1 (by decide)) (hC 2 (by decide)) (hC 3 (by decide)) hv hw
  have hdiff : |t * (a + b) / 2 - t * a / 2| = t * b / 2 := by
    rw [show t * (a + b) / 2 - t * a / 2 = t * b / 2 by ring,
      abs_of_nonneg (div_nonneg (mul_nonneg ht.1 hb.1) (by norm_num))]
  have hmoment : (∫ h, heat a (fun y => iteratedDeriv 2 (parisiRootSuffix ξ ms qs) y ^ 2) h ∂μh) =
      parisiRootUSpatialMoment 2 μh ξ ms qs 0 := by
    unfold parisiRootUSpatialMoment
    simp only [coleHopfSplitSpatialMoment_zero_eq, coleHopfQ_zero, mul_one]
    rfl
  rw [hdiff, hmoment] at HH
  simpa only [parisiRootSignedMoment, abs_zero, sub_self, add_zero, iteratedDeriv_one,
    a, b, show ∀ X : ℝ, 2 * X * (t * (deriv ξ |u| - deriv ξ 0) / 2) =
      t * (deriv ξ |u| - deriv ξ 0) * X from fun X => by ring] using HH

/-- A derivative increment from zero is controlled by the second
derivative at a positive upper endpoint. No positivity at zero is used. -/
theorem TalagrandXiCondition.deriv_sub_zero_le_second_mul_of_le {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {q x : ℝ} (hq : q ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) q) :
    deriv ξ x - deriv ξ 0 ≤ deriv (deriv ξ) q * x := by
  rcases eq_or_lt_of_le hx.1 with rfl | hx0
  · simp
  · have hinc := hξ.deriv_sub_le_second_mul ⟨hx.1, hx.2.trans hq.2⟩ ⟨le_rfl, hx.1⟩
    have hcurv := hξ.monotoneOn_second ⟨hx0, hx.2.trans hq.2⟩ hq hx.2
    simp only [sub_zero] at hinc
    exact hinc.trans (mul_le_mul_of_nonneg_right hcurv hx.1)

/-- The canonical signed root response has uniform linear separation
on the whole negative initial interval. Its covariance estimate and
curvature tolerance come from the actual Parisi recursion and full MIN. -/
theorem exists_uniform_parisi_root_signed_response_gap {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh) {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-(qs 0)) (0 : ℝ),
        (1 - t₀) / 2 * (qs 0 - u) ≤ parisiRootSignedResponseGap μh ξ ms qs t u := by
  obtain ⟨ε₁, hε₁, hgap⟩ := exists_uniform_parisi_root_nonnegative_response_gap hξ hμ ht₀
  obtain ⟨ε₂, hε₂, hcurv⟩ := exists_uniform_parisi_second_moment_curvature_tolerance hξ hμ
    (by linarith [ht₀.2] : 0 < (1 - t₀) / 2)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro k ms qs hm hmin hfull hnear t ht u hu
  have hnear₁ : randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε₁ :=
    hnear.trans_le (add_le_add le_rfl (min_le_left _ _))
  have hnear₂ : randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε₂ :=
    hnear.trans_le (add_le_add le_rfl (min_le_right _ _))
  have hqpos : 0 < qs 0 := by
    obtain ⟨hchain, _⟩ := randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
      ms qs hm hξ hμ hmin
    have hh := hchain 0 (by omega)
    rw [qExt_zero, qExt_succ_of_lt qs (Nat.succ_pos k)] at hh
    exact hh
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.2.le⟩
  have habs : |u| ≤ qs 0 := by rw [abs_of_nonpos hu.2]; linarith [hu.1]
  have hbase : (1 - t₀) / 2 * qs 0 ≤
      parisiRootUSpatialMoment 1 μh ξ ms qs (t * (deriv ξ (qs 0) - deriv ξ 0)) := by
    simpa only [parisiRootResponseGap, sub_zero] using
      hgap k ms qs hm hmin hfull hnear₁ t ht 0 ⟨le_rfl, hqpos.le⟩
  rw [← parisiRootSignedMoment_zero (μh := μh) hξ ms qs hmin.1 ht01] at hbase
  have hcov := (abs_le.1 (abs_parisiRootSignedMoment_sub_zero_le
    (μh := μh) hξ ms qs hmin.1 ht01 habs)).1
  have hinc := hξ.deriv_sub_zero_le_second_mul_of_le ⟨hqpos, (hmin.1.mem_Icc 0).2⟩
    ⟨abs_nonneg u, habs⟩
  have hMnonneg := parisiRootUSpatialMoment_nonneg 2 μh ξ ms qs 0
  have hscaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinc ht.1) hMnonneg
  have hc := (hcurv k ms qs hm hmin hfull hnear₂).1
  have htc := mul_le_mul_of_nonneg_left hc ht.1
  have htt := mul_le_mul_of_nonneg_right ht.2 (by linarith [ht₀.2] : 0 ≤ 1 + (1 - t₀) / 2)
  have hslope : t * deriv (deriv ξ) (qs 0) * parisiRootUSpatialMoment 2 μh ξ ms qs 0 ≤
      1 - (1 - t₀) / 2 := by nlinarith [sq_nonneg (1 - t₀)]
  have hprod := mul_le_mul_of_nonneg_right hslope (abs_nonneg u)
  rw [abs_of_nonpos hu.2] at hscaled hprod hcov
  unfold parisiRootSignedResponseGap
  nlinarith

end SpinGlass
