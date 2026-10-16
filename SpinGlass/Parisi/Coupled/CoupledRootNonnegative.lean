import SpinGlass.Parisi.Coupled.CoupledMainRoot

/-!
# The entire nonnegative initial overlap interval

The zero-mass curvature moment decreases with the split variance. Its
initial bound therefore controls the full initial interval, as in
Talagrand's (14.347)-(14.348), without a nearby-overlap restriction.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- Zero matching mass leaves only the negative squared third
derivative in the actual curvature dissipation. -/
theorem coleHopfSplitCurvatureDissipation_zero_nonpos (a : ℝ) (A : ℝ → ℝ) (x v : ℝ) :
    coleHopfSplitCurvatureDissipation 0 a A x v ≤ 0 := by
  unfold coleHopfSplitCurvatureDissipation
  simp only [mul_zero, zero_mul, zero_sub, coleHopfQ_zero, mul_one]
  exact integral_nonpos fun z => neg_nonpos.2 (sq_nonneg _)

/-- The actual zero-mass curvature moment is antitone on its full
admissible variance interval, including both endpoints. -/
theorem antitoneOn_coleHopfSplitSpatialMoment_two_zero {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv j A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|) (a x : ℝ) :
    AntitoneOn (coleHopfSplitSpatialMoment 2 0 a A x) (Icc (0 : ℝ) a) := by
  have hd := fun v (hv : v ∈ Icc (0 : ℝ) a) =>
    hasDerivWithinAt_coleHopfSplitSpatialMoment_two hA hb hLip (m := 0) hv x
  exact antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 a)
    (fun v hv => (hd v hv).continuousWithinAt)
    (fun v hv => (hd v (interior_subset hv)).mono interior_subset)
    (fun v _ => coleHopfSplitCurvatureDissipation_zero_nonpos a A x v)

/-- Antitonicity survives the actual probability field average. -/
theorem antitoneOn_parisiRootUSpatialMoment_two {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) :
    AntitoneOn (parisiRootUSpatialMoment 2 μh ξ ms qs)
      (Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) := by
  obtain ⟨hA, C, hC⟩ := parisiRootSuffix_spatial_regular_four ξ ms qs
  let a := deriv ξ (qs 0) - deriv ξ 0
  have hbound (v x : ℝ) : |coleHopfSplitSpatialMoment 2 0 a (parisiRootSuffix ξ ms qs) x v| ≤ 1 := by
    have hb := coleHopfSplitSpatialMoment_mem_Icc_of_sharp hA hC
      (parisiRootSuffix_sharp_spatial_bounds ξ qs hm) (abs_parisiRootSuffix_sub_le ξ ms qs)
      (m := 0) ⟨le_rfl, zero_le_one⟩ (by decide : 2 ∈ Finset.Icc 1 2) a v x
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hi (v : ℝ) : Integrable
      (fun x => coleHopfSplitSpatialMoment 2 0 a (parisiRootSuffix ξ ms qs) x v) μh :=
    Integrable.of_bound (continuous_coleHopfSplitSpatialMoment hA ⟨C, hC⟩
      (abs_parisiRootSuffix_sub_le ξ ms qs) (by decide : 2 ∈ Finset.Icc 1 4) 0 a v).measurable.aestronglyMeasurable
      1 (.of_forall fun x => by rw [Real.norm_eq_abs]; exact hbound v x)
  intro v hv w hw hvw
  unfold parisiRootUSpatialMoment
  exact integral_mono (hi w) (hi v) fun x =>
    antitoneOn_coleHopfSplitSpatialMoment_two_zero hA ⟨C, hC⟩
      (abs_parisiRootSuffix_sub_le ξ ms qs) a x hv hw hvw

theorem parisiRootUSpatialMoment_two_le_initial {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) :
    parisiRootUSpatialMoment 2 μh ξ ms qs v ≤ parisiRootUSpatialMoment 2 μh ξ ms qs 0 :=
  antitoneOn_parisiRootUSpatialMoment_two ξ ms qs hm ⟨le_rfl, hv.1.trans hv.2⟩ hv hv.1

/-- The root first moment has a global linear lower bound from its
actual derivative and the initial curvature moment. -/
theorem parisiRootUSpatialMoment_one_ge_linear {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (ha : 0 < deriv ξ (qs 0) - deriv ξ 0) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) :
    parisiRootUSpatialMoment 1 μh ξ ms qs 0 - parisiRootUSpatialMoment 2 μh ξ ms qs 0 * v ≤
      parisiRootUSpatialMoment 1 μh ξ ms qs v := by
  have hh := (convex_Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := parisiRootUSpatialMoment 1 μh ξ ms qs)
    (f' := fun w => -parisiRootUSpatialMoment 2 μh ξ ms qs w)
    (C := parisiRootUSpatialMoment 2 μh ξ ms qs 0)
    (fun w hw => hasDerivWithinAt_parisiRootUSpatialMoment_one ξ ms qs ha hw)
    (fun w hw => by
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (parisiRootUSpatialMoment_nonneg 2 μh ξ ms qs w)]
      exact parisiRootUSpatialMoment_two_le_initial ξ ms qs hm hw)
    (left_mem_Icc.2 ha.le) hv
  simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hv.1] at hh
  linarith [(abs_le.1 hh).1]

/-- The derivative increment is bounded by the curvature at its right
endpoint. Only positive interior points use ξ''' or curvature monotonicity. -/
theorem TalagrandXiCondition.deriv_sub_le_second_mul {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {u q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) q) :
    deriv ξ q - deriv ξ u ≤ deriv (deriv ξ) q * (q - u) := by
  rcases eq_or_lt_of_le hu.2 with rfl | huq
  · simp
  · have hsub : Icc u q ⊆ Icc (0 : ℝ) 1 := fun x hx => ⟨hu.1.trans hx.1, hx.2.trans hq.2⟩
    have hdiff : DifferentiableOn ℝ (deriv ξ) (Ioo u q) := fun x hx =>
      (hξ.hasDeriv_deriv x (hsub ⟨hx.1.le, hx.2.le⟩)).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, heq⟩ := exists_deriv_eq_slope (deriv ξ) huq (hξ.deriv_continuous.mono hsub) hdiff
    have hcurv := hξ.monotoneOn_second
      ⟨hu.1.trans_lt hc.1, hc.2.le.trans hq.2⟩ ⟨hu.1.trans_lt huq, hq.2⟩ hc.2.le
    rw [heq] at hcurv
    exact (div_le_iff₀ (sub_pos.2 huq)).1 hcurv

/-- Uniform linear response separation on the whole nonnegative
initial interval, with the tolerance chosen before MIN parameters and time. -/
theorem exists_uniform_parisi_root_nonnegative_response_gap {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh) {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (0 : ℝ) (qs 0),
        (1 - t₀) / 2 * (qs 0 - u) ≤ parisiRootResponseGap μh ξ ms qs t u := by
  obtain ⟨ε, hε, hcurv⟩ := exists_uniform_parisi_second_moment_curvature_tolerance hξ hμ
    (by linarith [ht₀.2] : 0 < (1 - t₀) / 2)
  refine ⟨ε, hε, ?_⟩
  intro k ms qs hm hmin hfull hnear t ht u hu
  obtain ⟨hchain, hstat⟩ := randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
    ms qs hm hξ hμ hmin
  have hqpos : 0 < qs 0 := by
    have hh := hchain 0 (by omega)
    rw [qExt_zero, qExt_succ_of_lt qs (Nat.succ_pos k)] at hh
    exact hh
  have ha : 0 < deriv ξ (qs 0) - deriv ξ 0 := sub_pos.2
    (hξ.strictMonoOn_deriv ⟨le_rfl, zero_le_one⟩ (hmin.1.mem_Icc 0) hqpos)
  have hM0 : parisiRootUSpatialMoment 1 μh ξ ms qs 0 = qs 0 := by
    rw [parisiRootUSpatialMoment_one_zero_eq_randomFieldParisiQMoment μh ξ ms qs hm, ← hstat 0]
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.2.le⟩
  have hv := parisi_root_time_variance_mem_Icc hξ qs hmin.1 ht01 hu
  have hlinear := parisiRootUSpatialMoment_one_ge_linear (μh := μh) ξ ms qs hm ha hv
  rw [hM0] at hlinear
  have hCnonneg := parisiRootUSpatialMoment_nonneg 2 μh ξ ms qs 0
  have hinc := hξ.deriv_sub_le_second_mul (hmin.1.mem_Icc 0) hu
  have hscaled := mul_le_mul_of_nonneg_left hinc ht.1
  have hscaledC := mul_le_mul_of_nonneg_right hscaled hCnonneg
  have hc := (hcurv k ms qs hm hmin hfull hnear).1
  have htc := mul_le_mul_of_nonneg_left hc ht.1
  have htt := mul_le_mul_of_nonneg_right ht.2 (by linarith [ht₀.2] : 0 ≤ 1 + (1 - t₀) / 2)
  have hslope : (1 - t₀) / 2 ≤ 1 - t * deriv (deriv ξ) (qs 0) * parisiRootUSpatialMoment 2 μh ξ ms qs 0 := by
    nlinarith [sq_nonneg (1 - t₀)]
  have hprod := mul_le_mul_of_nonneg_right hslope (sub_nonneg.2 hu.2)
  unfold parisiRootResponseGap
  nlinarith

/-- The original physical pressure has a uniform quadratic penalty
on the entire nonnegative initial interval. -/
theorem exists_uniform_randomFieldParisiAuxPairPressure_root_nonnegative_gap {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh) {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
        (Pm : Measure Ω) [IsProbabilityMeasure Pm], ∀ t ∈ Icc (0 : ℝ) t₀,
        ∀ G₀ : GaussianField (α := Config N) Pm
          (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
        ∀ u ∈ Icc (0 : ℝ) (qs 0),
          (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
          randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤
            2 * parisiInterpolationBracket μh ξ ms qs t - (1 - t₀) ^ 2 * (u - qs 0) ^ 2 / 8 := by
  obtain ⟨ε, hε, hgap⟩ := exists_uniform_parisi_root_nonnegative_response_gap hξ hμ ht₀
  refine ⟨ε, hε, ?_⟩
  intro k ms qs hm hmin hfull hnear N hN Ω _ Pm _ t ht G₀ u hu hreach
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.2.le⟩
  have hb := randomFieldParisiAuxPairPressure_root_le_gain hμ.integrable_id hN hξ ms qs hm hmin.1 ht01 hu G₀ hreach
  have hg := hgap k ms qs hm hmin hfull hnear t ht u hu
  have hnonneg : 0 ≤ (1 - t₀) / 2 * (qs 0 - u) :=
    mul_nonneg (by linarith [ht₀.2]) (sub_nonneg.2 hu.2)
  have hsquare := mul_self_le_mul_self hnonneg hg
  nlinarith

end SpinGlass
