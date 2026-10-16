import SpinGlass.Parisi.Variational.ParisiFirstOverlap
import SpinGlass.Parisi.Variational.ParisiVarianceTaylor
import SpinGlass.Parisi.Variational.ParisiQuantitativeMass
import SpinGlass.Parisi.Variational.ParisiProfileRemainder
import SpinGlass.Parisi.Variational.ParisiOuterEndpoints

/-!
# Concrete endpoint curvature for overlap variations

The identities underlying (14.283) are derived from the actual first and
second spatial moments. Endpoint differentiation is within the admissible
overlap interval. The variation functions here are twice the book's inserted
mass derivative, so their second derivatives have the corresponding factor.
Uniform profile continuity gives small quadratic overlap remainders and a
curvature tolerance selected before the MIN parameters. This is sufficient
for later smallness choices without asserting the sixth-root rate under the
preserved profile contract.
-/

open MeasureTheory Set

namespace SpinGlass

private theorem hasDerivWithinAt_stationary_profile_slope
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hqpos : 0 < q) {s t : Set ℝ}
    {M : ℝ → ℝ} {c : ℝ} (hM : HasDerivWithinAt M (-c) t 0) (hMq : M 0 = q)
    (hmaps : MapsTo (fun u => deriv ξ q - deriv ξ u) s t) :
    HasDerivWithinAt
      (fun u => deriv (deriv ξ) u * (u - M (deriv ξ q - deriv ξ u)))
      (deriv (deriv ξ) q * (1 - deriv (deriv ξ) q * c)) s q := by
  have hdv := (hξ.hasDeriv_deriv q hq).const_sub (deriv ξ q)
  have hM' : HasDerivWithinAt M (-c) t (deriv ξ q - deriv ξ q) := by
    simpa only [sub_self] using hM
  have hcomp := hM'.comp q hdv.hasDerivWithinAt hmaps
  have hprod := (hξ.hasDeriv_second q ⟨hqpos, hq.2⟩).hasDerivWithinAt.mul
    ((hasDerivAt_id q).hasDerivWithinAt.sub hcomp)
  convert! hprod using 1
  simp only [Pi.sub_apply, Function.comp_def, id_eq, sub_self, hMq, mul_zero, zero_add]
  ring

/-- Actual endpoint second derivative of the root f in (14.283).
The stationary first moment cancels the profile's third-derivative term. -/
theorem hasDerivWithinAt_derivWithin_parisiRootf_right_endpoint_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    HasDerivWithinAt
      (fun u => derivWithin (parisiRootf μh ξ ms qs) (Icc (0 : ℝ) (qs 0)) u)
      (deriv (deriv ξ) (qs 0) * (1 - deriv (deriv ξ) (qs 0) *
        parisiRootUSpatialMoment 2 μh ξ ms qs 0))
      (Icc (0 : ℝ) (qs 0)) (qs 0) := by
  have hqpos := randomFieldParisiQ_first_pos_of_isMin ms qs hμ.integrable_id hm hξ hμ hmin
  have ha : 0 < deriv ξ (qs 0) - deriv ξ 0 := sub_pos.2
    (hξ.strictMonoOn_deriv ⟨le_rfl, zero_le_one⟩ (hmin.1.mem_Icc 0) hqpos)
  have hM := hasDerivWithinAt_parisiRootUSpatialMoment_one (μh := μh) ξ ms qs ha
    (v := 0) ⟨le_rfl, ha.le⟩
  have hMq : parisiRootUSpatialMoment 1 μh ξ ms qs 0 = qs 0 := by
    rw [parisiRootUSpatialMoment_one_zero_eq_randomFieldParisiQMoment μh ξ ms qs hm]
    exact ((randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
      ms qs hm hξ hμ hmin).2 0).symm
  have hslope := hasDerivWithinAt_stationary_profile_slope hξ (hmin.1.mem_Icc 0)
    hqpos hM hMq (mapsTo_parisiRoot_variance_coordinate hξ (hmin.1.mem_Icc 0))
  apply hslope.congr_of_mem
  · intro u hu
    exact (hasDerivWithinAt_parisiRootf (μh := μh) hξ ms qs
      (hmin.1.mem_Icc 0) hqpos hu).derivWithin (uniqueDiffOn_Icc hqpos u hu)
  · exact ⟨hqpos.le, le_rfl⟩

/-- Derivative form of the actual root endpoint curvature formula (14.283). -/
theorem derivWithin_derivWithin_parisiRootf_right_endpoint_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    derivWithin (fun u => derivWithin (parisiRootf μh ξ ms qs) (Icc (0 : ℝ) (qs 0)) u)
      (Icc (0 : ℝ) (qs 0)) (qs 0) =
      deriv (deriv ξ) (qs 0) * (1 - deriv (deriv ξ) (qs 0) *
        parisiRootUSpatialMoment 2 μh ξ ms qs 0) := by
  have hqpos := randomFieldParisiQ_first_pos_of_isMin ms qs hμ.integrable_id hm hξ hμ hmin
  exact (hasDerivWithinAt_derivWithin_parisiRootf_right_endpoint_of_isMin
    ms qs hm hξ hμ hmin).derivWithin (uniqueDiffOn_Icc hqpos (qs 0) ⟨hqpos.le, le_rfl⟩)

/-- Actual endpoint second derivative of the nonroot f in (14.283), after
the field, root Gaussian and fixed-prefix averages. -/
theorem hasDerivWithinAt_derivWithin_parisiRightf_right_endpoint_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    HasDerivWithinAt
      (fun u => derivWithin (parisiRightf μh ξ ms qs p)
        (Icc (qs p.castSucc) (qs p.succ)) u)
      (deriv (deriv ξ) (qs p.succ) * (1 - deriv (deriv ξ) (qs p.succ) *
        parisiRightUSpatialMoment 2 μh ξ ms qs p 0))
      (Icc (qs p.castSucc) (qs p.succ)) (qs p.succ) := by
  have hqr : qs p.castSucc < qs p.succ :=
    hmin.1.1 (by change p.val < p.val + 1; omega)
  have hqpos : 0 < qs p.succ := lt_of_le_of_lt (hmin.1.mem_Icc p.castSucc).1 hqr
  have ha : 0 < deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) := sub_pos.2
    (hξ.strictMonoOn_deriv (hmin.1.mem_Icc p.castSucc) (hmin.1.mem_Icc p.succ) hqr)
  have hM := hasDerivWithinAt_parisiRightUSpatialMoment_one (μh := μh) hξ ms qs p hm hmin.1
    (v := 0) ⟨le_rfl, ha.le⟩
  have hMq : parisiRightUSpatialMoment 1 μh ξ ms qs p 0 = qs p.succ := by
    rw [parisiRightUSpatialMoment_one_zero_eq_randomFieldParisiQMoment hξ ms qs p hm hmin.1]
    exact ((randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
      ms qs hm hξ hμ hmin).2 p.succ).symm
  have hslope := hasDerivWithinAt_stationary_profile_slope hξ (hmin.1.mem_Icc p.succ)
    hqpos hM hMq
    (mapsTo_parisi_variance_coordinate hξ (hmin.1.mem_Icc p.castSucc) (hmin.1.mem_Icc p.succ))
  apply hslope.congr_of_mem
  · intro u hu
    exact (hasDerivWithinAt_parisiRightf (μh := μh) hξ ms qs p hm hmin.1 hu).derivWithin
      (uniqueDiffOn_Icc hqr u hu)
  · exact ⟨hqr.le, le_rfl⟩

/-- Derivative form of the concrete nonroot endpoint curvature (14.283). -/
theorem derivWithin_derivWithin_parisiRightf_right_endpoint_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    derivWithin (fun u => derivWithin (parisiRightf μh ξ ms qs p)
      (Icc (qs p.castSucc) (qs p.succ)) u) (Icc (qs p.castSucc) (qs p.succ)) (qs p.succ) =
      deriv (deriv ξ) (qs p.succ) * (1 - deriv (deriv ξ) (qs p.succ) *
        parisiRightUSpatialMoment 2 μh ξ ms qs p 0) := by
  have hqr : qs p.castSucc < qs p.succ :=
    hmin.1.1 (by change p.val < p.val + 1; omega)
  exact (hasDerivWithinAt_derivWithin_parisiRightf_right_endpoint_of_isMin
    ms qs p hm hξ hμ hmin).derivWithin
    (uniqueDiffOn_Icc hqr (qs p.succ) ⟨hqr.le, le_rfl⟩)

/-- Uniform overlap-coordinate version of the stationary Taylor estimate
(14.284), with any prescribed quadratic error in place of a claimed cubic
profile rate. The radius is selected before all MIN parameters. -/
theorem exists_uniform_parisi_f_overlap_quadratic_radius
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) (hμ : NondegenerateExternalFieldLaw μh)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      (∀ u ∈ Icc (0 : ℝ) (qs 0), qs 0 - u ≤ ρ →
        |parisiRootf μh ξ ms qs u -
          deriv (deriv ξ) (qs 0) * (1 - deriv (deriv ξ) (qs 0) *
            parisiRootUSpatialMoment 2 μh ξ ms qs 0) / 2 * (qs 0 - u) ^ 2| ≤
          κ * (qs 0 - u) ^ 2) ∧
      (∀ p : Fin k, ∀ u ∈ Icc (qs p.castSucc) (qs p.succ), qs p.succ - u ≤ ρ →
        |parisiRightf μh ξ ms qs p u -
          deriv (deriv ξ) (qs p.succ) * (1 - deriv (deriv ξ) (qs p.succ) *
            parisiRightUSpatialMoment 2 μh ξ ms qs p 0) / 2 * (qs p.succ - u) ^ 2| ≤
          κ * (qs p.succ - u) ^ 2) := by
  obtain ⟨a, ha, hsep⟩ := exists_uniform_parisiQ_first_lower_bound hξ hμ
  obtain ⟨σ, hσ, hTaylor⟩ :=
    hξ.exists_uniform_stationary_response_overlap_radius (half_pos ha) hκ
  refine ⟨min σ (a / 2), lt_min hσ (half_pos ha), ?_⟩
  intro k ms qs hm hmin
  have hfirst : a ≤ qs 0 := hsep k ms qs hm hmin
  have hq : ∀ r : Fin (k + 1), qs r ∈ Icc (a / 2) 1 := fun r =>
    ⟨(by linarith [hmin.1.monotone (Fin.zero_le r)]), (hmin.1.mem_Icc r).2⟩
  have hu : ∀ (r : Fin (k + 1)) (u : ℝ), u ≤ qs r → qs r - u ≤ min σ (a / 2) →
      u ∈ Icc (a / 2) 1 := by
    intro r u hur hdist
    exact ⟨by linarith [hmin.1.monotone (Fin.zero_le r),
      hdist.trans (min_le_right σ (a / 2))], hur.trans (hq r).2⟩
  constructor
  · intro u humem hdist
    apply hTaylor u (hu 0 u humem.2 hdist) (qs 0) (hq 0) humem.2
      (hdist.trans (min_le_left _ _)) _
      (parisiRootUSpatialMoment_mem_Icc ξ ms qs hm (by decide) 0)
    convert! abs_parisiRootf_sub_variance_quadratic_le_of_isMin ms qs hm hξ hμ hmin humem
      using 1
    congr 1
    ring
  · intro p u humem hdist
    apply hTaylor u (hu p.succ u humem.2 hdist) (qs p.succ) (hq p.succ) humem.2
      (hdist.trans (min_le_left _ _)) _
      (parisiRightUSpatialMoment_mem_Icc ξ ms qs p hm (by decide) 0)
    convert! abs_parisiRightf_sub_variance_quadratic_le_of_isMin ms qs p hm hξ hμ hmin humem
      using 1
    congr 1
    ring

/-- The two interval cases of (14.283) only need a uniform small quadratic
remainder. Short nonroot intervals use the exact left endpoint identity. -/
theorem curvature_ge_of_local_quadratic_remainder
    {f : ℝ → ℝ} {a q c κ δ ρ : ℝ}
    (haq : a < q) (hδ : 0 ≤ δ) (hρ : 0 < ρ)
    (hlower : ∀ u ∈ Icc a q, -δ ≤ f u)
    (htaylor : ∀ u ∈ Icc a q, q - u ≤ ρ →
      f u ≤ c / 2 * (q - u) ^ 2 + κ * (q - u) ^ 2)
    (hend : ρ ≤ q - a ∨ f a = 0) :
    -c ≤ 2 * δ / ρ ^ 2 + 2 * κ := by
  have hlong : ρ ≤ q - a → -c ≤ 2 * δ / ρ ^ 2 + 2 * κ := by
    intro h
    have hu : q - ρ ∈ Icc a q := ⟨by linarith, by linarith⟩
    have hh := (hlower _ hu).trans (htaylor _ hu (by linarith))
    rw [show q - (q - ρ) = ρ by ring] at hh
    have hcancel : (2 * δ / ρ ^ 2) * ρ ^ 2 = 2 * δ :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith [sq_pos_of_pos hρ]
  rcases hend with h | h
  · exact hlong h
  rcases le_or_gt ρ (q - a) with hlong' | hshort
  · exact hlong hlong'
  have hh := htaylor a ⟨le_rfl, haq.le⟩ hshort.le
  rw [h] at hh
  have hc : 0 ≤ c / 2 + κ := by
    apply (mul_nonneg_iff_of_pos_right (sq_pos_of_pos (sub_pos.2 haq))).1
    nlinarith
  have : 0 ≤ 2 * δ / ρ ^ 2 := by positivity
  linarith

/-- Uniform endpoint curvature control needed for the near-overlap cases of
Section 14.8. The MIN tolerance is selected from ξ, the nondegenerate field law
and the requested error before the level count or parameters. This is a
modulus-of-continuity substitute for the rate-specific bound (14.283). -/
theorem exists_uniform_parisi_endpoint_curvature_tolerance
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) (hμ : NondegenerateExternalFieldLaw μh)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      -(deriv (deriv ξ) (qs 0) * (1 - deriv (deriv ξ) (qs 0) *
        parisiRootUSpatialMoment 2 μh ξ ms qs 0)) ≤ κ ∧
      ∀ p : Fin k, -(deriv (deriv ξ) (qs p.succ) *
        (1 - deriv (deriv ξ) (qs p.succ) *
          parisiRightUSpatialMoment 2 μh ξ ms qs p 0)) ≤ κ := by
  obtain ⟨a, ha, hsep⟩ := exists_uniform_parisiQ_first_lower_bound hξ hμ
  obtain ⟨ρ, hρ, hTaylor⟩ :=
    exists_uniform_parisi_f_overlap_quadratic_radius hξ hμ (by positivity : 0 < κ / 4)
  obtain ⟨M₀, hM₀, hroot⟩ := exists_uniform_parisiRootf_lower_bound hξ
  obtain ⟨M₁, hM₁, hright⟩ := exists_uniform_parisiRightf_lower_bound hξ
  let r := min a ρ
  have hr : 0 < r := lt_min ha hρ
  let M := max M₀ M₁
  have hM : 0 < M := hM₀.trans_le (le_max_left _ _)
  let ε := (κ * r ^ 2 / 16) ^ 2 / M
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hMe : M * ε = (κ * r ^ 2 / 16) ^ 2 := by
    dsimp only [ε]
    field_simp
  have hsqrt : Real.sqrt (M * ε) = κ * r ^ 2 / 16 := by
    rw [hMe, Real.sqrt_sq (by positivity)]
  have hsmall : ∀ L : ℝ, L ≤ M → 4 * Real.sqrt (L * ε) ≤ κ * r ^ 2 / 4 := by
    intro L hL
    have hh := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hL hε.le)
    rw [hsqrt] at hh
    linarith
  have hbudget : 2 * (κ * r ^ 2 / 4) / r ^ 2 + 2 * (κ / 4) = κ := by
    field_simp; ring
  refine ⟨ε, hε, ?_⟩
  intro k ms qs hm hmin hfull hnear
  have hTaylor' := hTaylor k ms qs hm hmin
  constructor
  · have hq : 0 < qs 0 := ha.trans_le (hsep k ms qs hm hmin)
    have hh := curvature_ge_of_local_quadratic_remainder
      (c := deriv (deriv ξ) (qs 0) * (1 - deriv (deriv ξ) (qs 0) *
        parisiRootUSpatialMoment 2 μh ξ ms qs 0)) (κ := κ / 4) hq
      (by positivity : 0 ≤ κ * r ^ 2 / 4) hr
      (fun u hu => (neg_le_neg (hsmall M₀ (le_max_left _ _))).trans
        (hroot hμ.integrable_id hm hmin hε.le hnear u hu))
      (fun u hu hdist => by
        have hh := (le_abs_self _).trans
          (hTaylor'.1 u hu (hdist.trans (min_le_right _ _)))
        linarith)
      (Or.inl (by simpa only [sub_zero] using
        (min_le_left a ρ).trans (hsep k ms qs hm hmin)))
    rwa [hbudget] at hh
  · intro p
    have hq : qs p.castSucc < qs p.succ :=
      hmin.1.1 (by change p.val < p.val + 1; omega)
    have hh := curvature_ge_of_local_quadratic_remainder
      (c := deriv (deriv ξ) (qs p.succ) * (1 - deriv (deriv ξ) (qs p.succ) *
        parisiRightUSpatialMoment 2 μh ξ ms qs p 0)) (κ := κ / 4) hq
      (by positivity : 0 ≤ κ * r ^ 2 / 4) hr
      (fun u hu => (neg_le_neg (hsmall M₁ (le_max_right _ _))).trans
        (hright hμ.integrable_id hm hmin.1 hfull hε.le hnear p u hu))
      (fun u hu hdist => by
        have hh := (le_abs_self _).trans
          (hTaylor'.2 p u hu (hdist.trans (min_le_right _ _)))
        linarith)
      (Or.inr (parisiRightf_left_endpoint_eq_zero_of_isMinOn hμ.integrable_id
        hξ ms qs p hm hmin.1 hfull))
    rwa [hbudget] at hh

/-- Consumer form of the overlap curvature estimate: ξ''(q) times the actual
second spatial moment is at most one plus any prescribed positive error.
This supplies the tolerance choice used by the near-overlap main estimates. -/
theorem exists_uniform_parisi_second_moment_curvature_tolerance
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) (hμ : NondegenerateExternalFieldLaw μh)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      deriv (deriv ξ) (qs 0) * parisiRootUSpatialMoment 2 μh ξ ms qs 0 ≤ 1 + κ ∧
      ∀ p : Fin k, deriv (deriv ξ) (qs p.succ) *
        parisiRightUSpatialMoment 2 μh ξ ms qs p 0 ≤ 1 + κ := by
  obtain ⟨a, ha, hsep⟩ := exists_uniform_parisiQ_first_lower_bound hξ hμ
  let b := min a (1 / 2)
  have hb : 0 < b := lt_min ha (by norm_num)
  have hb1 : b ≤ 1 := (min_le_right a (1 / 2)).trans (by norm_num)
  let d := deriv (deriv ξ) b
  have hd : 0 < d := hξ.second_pos b ⟨hb.le, hb1⟩ (ne_of_gt hb)
  obtain ⟨ε, hε, hcurvature⟩ :=
    exists_uniform_parisi_endpoint_curvature_tolerance hξ hμ (mul_pos hκ hd)
  have hconvert : ∀ q ∈ Icc b 1, ∀ m : ℝ,
      -(deriv (deriv ξ) q * (1 - deriv (deriv ξ) q * m)) ≤ κ * d →
      deriv (deriv ξ) q * m ≤ 1 + κ := by
    intro q hq m hcurv
    have hDpos := hξ.second_pos q ⟨hb.le.trans hq.1, hq.2⟩
      (ne_of_gt (hb.trans_le hq.1))
    have hDge : d ≤ deriv (deriv ξ) q :=
      hξ.monotoneOn_second ⟨hb, hb1⟩ ⟨hb.trans_le hq.1, hq.2⟩ hq.1
    have hh : deriv (deriv ξ) q * (deriv (deriv ξ) q * m - (1 + κ)) ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_left hDge hκ.le]
    exact sub_nonpos.1 ((mul_nonpos_iff_pos_imp_nonpos.1 hh).1 hDpos)
  refine ⟨ε, hε, ?_⟩
  intro k ms qs hm hmin hfull hnear
  have hq : ∀ r : Fin (k + 1), qs r ∈ Icc b 1 := fun r =>
    ⟨((min_le_left a (1 / 2)).trans (hsep k ms qs hm hmin)).trans
      (hmin.1.monotone (Fin.zero_le r)), (hmin.1.mem_Icc r).2⟩
  have hh := hcurvature k ms qs hm hmin hfull hnear
  exact ⟨hconvert _ (hq 0) _ hh.1, fun p => hconvert _ (hq p.succ) _ (hh.2 p)⟩

/-- The mirror second-moment bound uses exactly the same MIN tolerance as
the root/nonroot estimate. The initial outer moment is transported from the
old interval, so the terminal outer split is included without varying its
fixed old mass one. -/
theorem exists_uniform_parisi_outer_second_moment_curvature_tolerance
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) (hμ : NondegenerateExternalFieldLaw μh)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ p : Fin (k + 1), deriv (deriv ξ) (qs p) *
        parisiLeftUSpatialMoment 2 μh ξ ms qs p 0 ≤ 1 + κ := by
  obtain ⟨ε, hε, hcurv⟩ := exists_uniform_parisi_second_moment_curvature_tolerance hξ hμ hκ
  refine ⟨ε, hε, ?_⟩
  intro k ms qs hm hmin hfull hnear p
  have hh := hcurv k ms qs hm hmin hfull hnear
  refine Fin.cases ?_ (fun r => ?_) p
  · rw [parisiLeftUSpatialMoment_first_zero_eq_parisiRootUSpatialMoment 2 (by decide)]
    exact hh.1
  · rw [parisiLeftUSpatialMoment_succ_zero_eq_parisiRightUSpatialMoment 2 (by decide)
      μh ξ ms qs r hm]
    exact hh.2 r

/-- Actual mirror endpoint curvature: the stationary first moment cancels
the third-profile-derivative term at the left overlap. The curvature formula
uses only an admissible one-sided variance derivative and includes the
terminal fixed mass one. -/
theorem hasDerivWithinAt_derivWithin_parisiLeftf_left_endpoint_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    HasDerivWithinAt
      (fun u => derivWithin (parisiLeftf μh ξ ms qs p)
        (Icc (qs p) (qExt qs (p.val + 2))) u)
      (deriv (deriv ξ) (qs p) * (deriv (deriv ξ) (qs p) *
        parisiLeftUSpatialMoment 2 μh ξ ms qs p 0 - 1))
      (Icc (qs p) (qExt qs (p.val + 2))) (qs p) := by
  have hgap := parisi_outer_overlap_gap_of_isMin ms qs p hm hξ hμ hmin
  have hqpos : 0 < qs p :=
    (randomFieldParisiQ_first_pos_of_isMin ms qs hμ.integrable_id hm hξ hμ hmin).trans_le
      (hmin.1.monotone (Fin.zero_le p))
  have hR := qExt_mem_Icc hmin.1.monotone hmin.1.2.1 hmin.1.2.2 (p.val + 2)
  have ha : 0 < deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) := sub_pos.2
    (hξ.strictMonoOn_deriv (hmin.1.mem_Icc p) hR hgap)
  have hM := hasDerivWithinAt_parisiLeftUSpatialMoment_one (μh := μh) hξ ms qs p hm hmin.1
    hgap (w := 0) ⟨le_rfl, ha.le⟩
  have hMq : parisiLeftUSpatialMoment 1 μh ξ ms qs p 0 = qs p := by
    rw [parisiLeftUSpatialMoment_one_zero_eq_randomFieldParisiQMoment hξ ms qs p hm hmin.1]
    exact ((randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
      ms qs hm hξ hμ hmin).2 p).symm
  have hdw := (hξ.hasDeriv_deriv (qs p) (hmin.1.mem_Icc p)).sub_const (deriv ξ (qs p))
  have hM' : HasDerivWithinAt (parisiLeftUSpatialMoment 1 μh ξ ms qs p)
      (parisiLeftUSpatialMoment 2 μh ξ ms qs p 0)
      (Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p)))
      (deriv ξ (qs p) - deriv ξ (qs p)) := by simpa only [sub_self] using hM
  have hcomp := hM'.comp (qs p) hdw.hasDerivWithinAt
    (mapsTo_parisi_outer_variance_coordinate hξ (hmin.1.mem_Icc p) hR)
  have hprod := (hξ.hasDeriv_second (qs p) ⟨hqpos, (hmin.1.mem_Icc p).2⟩).hasDerivWithinAt.mul
    (hcomp.sub (hasDerivAt_id (qs p)).hasDerivWithinAt)
  have hslope : HasDerivWithinAt
      (fun u => deriv (deriv ξ) u * (parisiLeftUSpatialMoment 1 μh ξ ms qs p
        (deriv ξ u - deriv ξ (qs p)) - u))
      (deriv (deriv ξ) (qs p) * (deriv (deriv ξ) (qs p) *
        parisiLeftUSpatialMoment 2 μh ξ ms qs p 0 - 1))
      (Icc (qs p) (qExt qs (p.val + 2))) (qs p) := by
    convert! hprod using 1
    simp only [Pi.sub_apply, Function.comp_def, id_eq, sub_self, hMq, mul_zero, zero_add]
    ring
  apply hslope.congr_of_mem
  · intro u hu
    exact (hasDerivWithinAt_parisiLeftf (μh := μh) hξ ms qs p hm hmin.1 hgap hu).derivWithin
      (uniqueDiffOn_Icc hgap u hu)
  · exact ⟨le_rfl, hgap.le⟩

/-- Derivative form of the concrete mirror endpoint curvature formula. -/
theorem derivWithin_derivWithin_parisiLeftf_left_endpoint_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    derivWithin (fun u => derivWithin (parisiLeftf μh ξ ms qs p)
      (Icc (qs p) (qExt qs (p.val + 2))) u) (Icc (qs p) (qExt qs (p.val + 2))) (qs p) =
      deriv (deriv ξ) (qs p) * (deriv (deriv ξ) (qs p) *
        parisiLeftUSpatialMoment 2 μh ξ ms qs p 0 - 1) := by
  have hgap := parisi_outer_overlap_gap_of_isMin ms qs p hm hξ hμ hmin
  exact (hasDerivWithinAt_derivWithin_parisiLeftf_left_endpoint_of_isMin
    ms qs p hm hξ hμ hmin).derivWithin (uniqueDiffOn_Icc hgap (qs p) ⟨le_rfl, hgap.le⟩)

/-- Mirror overlap-coordinate remainder for the actual stationary f. The
radius is selected from ξ, the field law and the requested error before
all MIN parameters, and applies to the terminal outer split as well. -/
theorem exists_uniform_parisi_outer_f_overlap_quadratic_radius
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) (hμ : NondegenerateExternalFieldLaw μh)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      ∀ p : Fin (k + 1), ∀ u ∈ Icc (qs p) (qExt qs (p.val + 2)), u - qs p ≤ ρ →
        |parisiLeftf μh ξ ms qs p u -
          deriv (deriv ξ) (qs p) * (deriv (deriv ξ) (qs p) *
            parisiLeftUSpatialMoment 2 μh ξ ms qs p 0 - 1) / 2 * (u - qs p) ^ 2| ≤
          κ * (u - qs p) ^ 2 := by
  obtain ⟨a, ha, hsep⟩ := exists_uniform_parisiQ_first_lower_bound hξ hμ
  obtain ⟨ρ, hρ, hTaylor⟩ := hξ.exists_uniform_stationary_outer_response_overlap_radius ha hκ
  refine ⟨ρ, hρ, ?_⟩
  intro k ms qs hm hmin p u hu hdist
  have hq : qs p ∈ Icc a 1 :=
    ⟨(hsep k ms qs hm hmin).trans (hmin.1.monotone (Fin.zero_le p)),
      (hmin.1.mem_Icc p).2⟩
  have humem : u ∈ Icc a 1 :=
    ⟨hq.1.trans hu.1, hu.2.trans (qExt_mem_Icc hmin.1.monotone hmin.1.2.1 hmin.1.2.2 _).2⟩
  apply hTaylor (qs p) hq u humem hu.1 hdist _
    (parisiLeftUSpatialMoment_mem_Icc ξ ms qs p hm (by decide) 0)
  exact abs_parisiLeftf_sub_variance_quadratic_le_of_isMin ms qs p hm hξ hμ hmin hu

end SpinGlass
