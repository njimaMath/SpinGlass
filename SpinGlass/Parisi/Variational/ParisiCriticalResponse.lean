import SpinGlass.Parisi.Variational.ParisiOverlapCurvature

/-!
# Concrete response gaps for the critical coupled cases

The moments here are the actual field-averaged Parisi spatial moments. Their
linear variance remainders and curvature tolerance supply the response gap
in (14.325)-(14.332) and its mirror counterpart. Identifying this gap with
the derivative of the coupled recursion remains a separate adapter.
-/

open MeasureTheory Set

namespace SpinGlass

/-- A uniformly Lipschitz derivative gives a quadratic remainder on the
closed variance interval, including its one-sided endpoints. -/
theorem abs_moment_sub_linear_le_of_derivative_lipschitz
    {F G : ℝ → ℝ} {a L v : ℝ} (hL : 0 ≤ L)
    (hF : ∀ t ∈ Icc 0 a, HasDerivWithinAt F (G t) (Icc 0 a) t)
    (hG : ∀ t ∈ Icc 0 a, ∀ s ∈ Icc 0 a, |G t - G s| ≤ L * |t - s|)
    (hv : v ∈ Icc 0 a) :
    |F v - F 0 - G 0 * v| ≤ L * v ^ 2 := by
  have hsub : Icc (0 : ℝ) v ⊆ Icc 0 a := Icc_subset_Icc le_rfl hv.2
  have hh := (convex_Icc (0 : ℝ) v).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => F t - F 0 - G 0 * t) (f' := fun t => G t - G 0) (C := L * v)
    (fun t ht => ((((hF t (hsub ht)).mono hsub).sub_const (F 0)).sub
      ((hasDerivWithinAt_id t _).const_mul (G 0))).congr_deriv (by simp))
    (fun t ht => by
      rw [Real.norm_eq_abs]
      have hb := hG t (hsub ht) 0 ⟨le_rfl, hv.1.trans hv.2⟩
      rw [sub_zero, abs_of_nonneg ht.1] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left ht.2 hL))
    (show (0 : ℝ) ∈ Icc (0 : ℝ) v from ⟨le_rfl, hv.1⟩)
    (show v ∈ Icc (0 : ℝ) v from ⟨hv.1, le_rfl⟩)
  simpa only [sub_self, mul_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg hv.1,
    mul_assoc, pow_two] using hh

/-- The actual root first moment has a uniform quadratic variance remainder. -/
theorem abs_parisiRootUSpatialMoment_one_sub_linear_le
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (ha : 0 < deriv ξ (qs 0) - deriv ξ 0) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) :
    |parisiRootUSpatialMoment 1 μh ξ ms qs v - parisiRootUSpatialMoment 1 μh ξ ms qs 0 +
      parisiRootUSpatialMoment 2 μh ξ ms qs 0 * v| ≤ 146 * v ^ 2 := by
  have hh := abs_moment_sub_linear_le_of_derivative_lipschitz
    (G := fun t => -parisiRootUSpatialMoment 2 μh ξ ms qs t) (by norm_num : (0 : ℝ) ≤ 146)
    (fun t ht => hasDerivWithinAt_parisiRootUSpatialMoment_one (μh := μh) ξ ms qs ha ht)
    (fun t ht s hs => by simpa only [neg_sub_neg, abs_sub_comm] using
      abs_parisiRootUSpatialMoment_two_sub_le (μh := μh) ξ ms qs hm ht hs) hv
  simpa only [neg_mul, sub_neg_eq_add] using hh

/-- The nonroot first moment has the same level-independent variance error. -/
theorem abs_parisiRightUSpatialMoment_one_sub_linear_le
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) :
    |parisiRightUSpatialMoment 1 μh ξ ms qs p v - parisiRightUSpatialMoment 1 μh ξ ms qs p 0 +
      parisiRightUSpatialMoment 2 μh ξ ms qs p 0 * v| ≤ 146 * v ^ 2 := by
  have hh := abs_moment_sub_linear_le_of_derivative_lipschitz
    (G := fun t => -parisiRightUSpatialMoment 2 μh ξ ms qs p t)
    (by norm_num : (0 : ℝ) ≤ 146)
    (fun t ht => hasDerivWithinAt_parisiRightUSpatialMoment_one (μh := μh) hξ ms qs p hm hq ht)
    (fun t ht s hs => by simpa only [neg_sub_neg, abs_sub_comm] using
      abs_parisiRightUSpatialMoment_two_sub_le (μh := μh) hξ ms qs p hm hq ht hs) hv
  simpa only [neg_mul, sub_neg_eq_add] using hh

/-- The outer first moment has a positive linear term with the same
quadratic error, including terminal mass one and both variance endpoints. -/
theorem abs_parisiLeftUSpatialMoment_one_sub_linear_le
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hgap : qs p < qExt qs (p.val + 2)) {w : ℝ}
    (hw : w ∈ Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) :
    |parisiLeftUSpatialMoment 1 μh ξ ms qs p w - parisiLeftUSpatialMoment 1 μh ξ ms qs p 0 -
      parisiLeftUSpatialMoment 2 μh ξ ms qs p 0 * w| ≤ 146 * w ^ 2 := by
  exact abs_moment_sub_linear_le_of_derivative_lipschitz (by norm_num : (0 : ℝ) ≤ 146)
    (fun t ht => hasDerivWithinAt_parisiLeftUSpatialMoment_one (μh := μh) hξ ms qs p hm hq hgap ht)
    (fun t ht s hs => abs_parisiLeftUSpatialMoment_two_sub_le hξ ms qs p hm hq hgap ht hs) hw

/-- Concrete root response gap in (14.325). -/
noncomputable def parisiRootResponseGap (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u : ℝ) : ℝ :=
  parisiRootUSpatialMoment 1 μh ξ ms qs (t * (deriv ξ (qs 0) - deriv ξ u)) - u

/-- Concrete nonroot response gap in (14.325), after all prefix averages. -/
noncomputable def parisiRightResponseGap (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (t u : ℝ) : ℝ :=
  parisiRightUSpatialMoment 1 μh ξ ms qs p (t * (deriv ξ (qs p.succ) - deriv ξ u)) - u

/-- Mirror response gap for the outer split, including its terminal interval. -/
noncomputable def parisiLeftResponseGap (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t u : ℝ) : ℝ :=
  parisiLeftUSpatialMoment 1 μh ξ ms qs p (t * (deriv ξ u - deriv ξ (qs p))) - u

/-- Scalar critical-case estimate. A profile modulus and a quadratic moment
remainder convert a strictly negative endpoint slope into a uniform gap. -/
theorem response_gap_ge_of_quadratic_remainder
    {b Δ v c D t δ B η : ℝ} (hΔ : 0 ≤ Δ) (hη : 0 ≤ η)
    (hc : c ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) (B * Δ))
    (hlinear : δ / 2 ≤ 1 - t * D * c)
    (hvariance : |v - D * Δ| ≤ η * Δ)
    (hresponse : |b - (Δ - c * (t * v))| ≤ 146 * (t * v) ^ 2)
    (hsmall : η + 146 * B ^ 2 * Δ ≤ δ / 4) :
    δ / 4 * Δ ≤ b := by
  have hct : c * t ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hc.1 ht.1, (mul_le_mul_of_nonneg_left ht.2 hc.1).trans (by simpa using hc.2)⟩
  have hprofile : c * t * (v - D * Δ) ≤ η * Δ := by
    calc
      c * t * (v - D * Δ) ≤ |c * t * (v - D * Δ)| := le_abs_self _
      _ = c * t * |v - D * Δ| := by rw [abs_mul, abs_of_nonneg hct.1]
      _ ≤ c * t * (η * Δ) := mul_le_mul_of_nonneg_left hvariance hct.1
      _ ≤ η * Δ := mul_le_of_le_one_left (mul_nonneg hη hΔ) hct.2
  have htv : t * v ∈ Icc (0 : ℝ) (B * Δ) :=
    ⟨mul_nonneg ht.1 hv.1, (mul_le_of_le_one_left hv.1 ht.2).trans hv.2⟩
  have hcubic : 146 * (t * v) ^ 2 ≤ 146 * B ^ 2 * Δ ^ 2 := by
    simpa only [mul_pow, mul_assoc] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htv.1 htv.2 2) (by norm_num : (0 : ℝ) ≤ 146)
  have hlow := neg_le_of_abs_le hresponse
  have hs := mul_le_mul_of_nonneg_right hsmall hΔ
  have hl := mul_le_mul_of_nonneg_right hlinear hΔ
  nlinarith

/-- Uniform critical response separation in (14.332), for both mass
orientations. The MIN tolerance and overlap radius are chosen from ξ, the
nondegenerate field law and t₀ before all levels, parameters and times. The
outer conclusion includes the terminal index and k=0. This is the scalar
input to the coupled estimate; it does not assume its coupling derivative. -/
theorem exists_uniform_parisi_critical_response_gap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) (hμ : NondegenerateExternalFieldLaw μh)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
        ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
        IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
          (parisiParameterDomain k) (ms, qs) →
        randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
        ∀ t ∈ Icc (0 : ℝ) t₀,
          (∀ u ∈ Icc (0 : ℝ) (qs 0), qs 0 - u ≤ ρ →
            (1 - t₀) / 4 * (qs 0 - u) ≤ parisiRootResponseGap μh ξ ms qs t u) ∧
          (∀ p : Fin k, ∀ u ∈ Icc (qs p.castSucc) (qs p.succ), qs p.succ - u ≤ ρ →
            (1 - t₀) / 4 * (qs p.succ - u) ≤ parisiRightResponseGap μh ξ ms qs p t u) ∧
          (∀ p : Fin (k + 1), ∀ u ∈ Icc (qs p) (qExt qs (p.val + 2)), u - qs p ≤ ρ →
            parisiLeftResponseGap μh ξ ms qs p t u ≤ -(1 - t₀) / 4 * (u - qs p)) := by
  let δ := 1 - t₀
  have hδ : 0 < δ := sub_pos.2 ht₀.2
  have hδ1 : δ ≤ 1 := by dsimp only [δ]; linarith [ht₀.1]
  let B := deriv (deriv ξ) 1
  have hB : 0 < B := hξ.second_pos 1 ⟨zero_le_one, le_rfl⟩ one_ne_zero
  let η := δ / 8
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨a, ha, hsep⟩ := exists_uniform_parisiQ_first_lower_bound hξ hμ
  obtain ⟨σ, hσ, hmod⟩ := hξ.exists_uniform_second_radius (half_pos ha) hη
  obtain ⟨ε₀, hε₀, hcurv₀⟩ :=
    exists_uniform_parisi_second_moment_curvature_tolerance hξ hμ (half_pos hδ)
  obtain ⟨ε₁, hε₁, hcurv₁⟩ :=
    exists_uniform_parisi_outer_second_moment_curvature_tolerance hξ hμ (half_pos hδ)
  let ρ := min (a / 2) (min σ (δ / (1168 * B ^ 2)))
  have hρ : 0 < ρ := lt_min (half_pos ha) (lt_min hσ (by positivity))
  have hρa : ρ ≤ a / 2 := min_le_left _ _
  have hρσ : ρ ≤ σ := (min_le_right _ _).trans (min_le_left _ _)
  have hρδ : ρ ≤ δ / (1168 * B ^ 2) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : ∀ Δ : ℝ, Δ ≤ ρ → η + 146 * B ^ 2 * Δ ≤ δ / 4 := by
    intro Δ hΔ
    have hh := (le_div_iff₀ (by positivity : 0 < 1168 * B ^ 2)).1 (hΔ.trans hρδ)
    dsimp only [η]
    nlinarith
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, ρ, hρ, ?_⟩
  intro k ms qs hm hmin hfull hnear t ht
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.2.le⟩
  have hscale : ∀ {v A : ℝ}, v ∈ Icc (0 : ℝ) A → t * v ∈ Icc (0 : ℝ) A := by
    intro v A hv
    exact ⟨mul_nonneg ht.1 hv.1, (mul_le_of_le_one_left hv.1 ht01.2).trans hv.2⟩
  have hc₀ := hcurv₀ k ms qs hm hmin hfull
    (hnear.trans_le (add_le_add le_rfl (min_le_left ε₀ ε₁)))
  have hc₁ := hcurv₁ k ms qs hm hmin hfull
    (hnear.trans_le (add_le_add le_rfl (min_le_right ε₀ ε₁)))
  have hq : ∀ p : Fin (k + 1), qs p ∈ Icc (a / 2) 1 := fun p =>
    ⟨(half_le_self ha.le).trans ((hsep k ms qs hm hmin).trans
      (hmin.1.monotone (Fin.zero_le p))), (hmin.1.mem_Icc p).2⟩
  have hpositive : ∀ p : Fin (k + 1), 0 < qs p := fun p => (half_pos ha).trans_le (hq p).1
  have hstat := (randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
    ms qs hm hξ hμ hmin).2
  have hslope : ∀ (q c : ℝ), deriv (deriv ξ) q * c ≤ 1 + δ / 2 →
      δ / 2 ≤ 1 - t * deriv (deriv ξ) q * c := by
    intro q c hc
    have hh := mul_le_mul_of_nonneg_left hc ht.1
    have hh' := mul_le_mul_of_nonneg_right ht.2 (by positivity : 0 ≤ 1 + δ / 2)
    dsimp only [δ] at hh hh' hδ1 ⊢
    nlinarith [sq_nonneg (1 - t₀)]
  have hinner : ∀ (q u c b : ℝ), q ∈ Icc (a / 2) 1 → u ∈ Icc (a / 2) 1 →
      u ≤ q → q - u ≤ ρ → c ∈ Icc (0 : ℝ) 1 →
      deriv (deriv ξ) q * c ≤ 1 + δ / 2 →
      |b - (q - u - c * (t * (deriv ξ q - deriv ξ u)))| ≤
        146 * (t * (deriv ξ q - deriv ξ u)) ^ 2 → δ / 4 * (q - u) ≤ b := by
    intro q u c b hq' hu' huq hdist hc hcurv hrem
    have hsecond : ∀ x ∈ Icc u q,
        |deriv (deriv ξ) x - deriv (deriv ξ) q| ≤ η := by
      intro x hx
      apply hmod x ⟨hu'.1.trans hx.1, hx.2.trans hq'.2⟩ q hq'
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hx.2)]
      exact (sub_le_sub_left hx.1 q).trans (hdist.trans hρσ)
    exact response_gap_ge_of_quadratic_remainder (sub_nonneg.2 huq) hη.le hc ht01
      (parisi_variance_mem_Icc_linear hξ ((half_pos ha).trans_le hu'.1) hq'.2 huq)
      (hslope q c hcurv)
      (abs_parisi_variance_sub_linear_le hξ ((half_pos ha).le.trans hu'.1) hq'.2 huq hsecond)
      hrem (hsmall _ hdist)
  have houter : ∀ (q u c b : ℝ), q ∈ Icc (a / 2) 1 → u ∈ Icc (a / 2) 1 →
      q ≤ u → u - q ≤ ρ → c ∈ Icc (0 : ℝ) 1 →
      deriv (deriv ξ) q * c ≤ 1 + δ / 2 →
      |-b - (u - q - c * (t * (deriv ξ u - deriv ξ q)))| ≤
        146 * (t * (deriv ξ u - deriv ξ q)) ^ 2 → b ≤ -δ / 4 * (u - q) := by
    intro q u c b hq' hu' hqu hdist hc hcurv hrem
    have hsecond : ∀ x ∈ Icc q u,
        |deriv (deriv ξ) x - deriv (deriv ξ) q| ≤ η := by
      intro x hx
      apply hmod x ⟨hq'.1.trans hx.1, hx.2.trans hu'.2⟩ q hq'
      rw [abs_of_nonneg (sub_nonneg.2 hx.1)]
      exact (sub_le_sub_right hx.2 q).trans (hdist.trans hρσ)
    have hh := response_gap_ge_of_quadratic_remainder (sub_nonneg.2 hqu) hη.le hc ht01
      (parisi_variance_mem_Icc_linear hξ ((half_pos ha).trans_le hq'.1) hu'.2 hqu)
      (hslope q c hcurv)
      (abs_parisi_outer_variance_sub_linear_le hξ ((half_pos ha).le.trans hq'.1) hu'.2 hqu
        hsecond) hrem (hsmall _ hdist)
    linarith
  have hleftmem : ∀ (p : Fin (k + 1)) (u : ℝ), u ≤ qs p → qs p - u ≤ ρ →
      u ∈ Icc (a / 2) 1 := by
    intro p u hu hdist
    have hqa := (hsep k ms qs hm hmin).trans (hmin.1.monotone (Fin.zero_le p))
    exact ⟨by linarith [hdist.trans hρa], hu.trans (hq p).2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u hu hdist
    have haRoot : 0 < deriv ξ (qs 0) - deriv ξ 0 := sub_pos.2
      (hξ.strictMonoOn_deriv ⟨le_rfl, zero_le_one⟩ (hmin.1.mem_Icc 0) (hpositive 0))
    have hM0 : parisiRootUSpatialMoment 1 μh ξ ms qs 0 = qs 0 := by
      rw [parisiRootUSpatialMoment_one_zero_eq_randomFieldParisiQMoment μh ξ ms qs hm,
        ← hstat 0]
    apply hinner (qs 0) u (parisiRootUSpatialMoment 2 μh ξ ms qs 0)
      (parisiRootResponseGap μh ξ ms qs t u) (hq 0) (hleftmem 0 u hu.2 hdist) hu.2 hdist
      (parisiRootUSpatialMoment_mem_Icc ξ ms qs hm (by decide) 0) hc₀.1
    have hh := abs_parisiRootUSpatialMoment_one_sub_linear_le (μh := μh) ξ ms qs hm haRoot
      (hscale (mapsTo_parisiRoot_variance_coordinate hξ (hmin.1.mem_Icc 0) hu))
    rw [hM0] at hh
    convert! hh using 1
    congr 1
    dsimp only [parisiRootResponseGap]
    ring
  · intro p u hu hdist
    have hM0 : parisiRightUSpatialMoment 1 μh ξ ms qs p 0 = qs p.succ := by
      rw [parisiRightUSpatialMoment_one_zero_eq_randomFieldParisiQMoment hξ ms qs p hm hmin.1,
        ← hstat p.succ]
    apply hinner (qs p.succ) u (parisiRightUSpatialMoment 2 μh ξ ms qs p 0)
      (parisiRightResponseGap μh ξ ms qs p t u) (hq p.succ) (hleftmem p.succ u hu.2 hdist)
      hu.2 hdist (parisiRightUSpatialMoment_mem_Icc ξ ms qs p hm (by decide) 0) (hc₀.2 p)
    have hh := abs_parisiRightUSpatialMoment_one_sub_linear_le (μh := μh) hξ ms qs p hm hmin.1
      (hscale (mapsTo_parisi_variance_coordinate hξ (hmin.1.mem_Icc p.castSucc)
        (hmin.1.mem_Icc p.succ) hu))
    rw [hM0] at hh
    convert! hh using 1
    congr 1
    dsimp only [parisiRightResponseGap]
    ring
  · intro p u hu hdist
    have hgap := parisi_outer_overlap_gap_of_isMin ms qs p hm hξ hμ hmin
    have hR := qExt_mem_Icc hmin.1.monotone hmin.1.2.1 hmin.1.2.2 (p.val + 2)
    have humem : u ∈ Icc (a / 2) 1 := ⟨(hq p).1.trans hu.1, hu.2.trans hR.2⟩
    have hM0 : parisiLeftUSpatialMoment 1 μh ξ ms qs p 0 = qs p := by
      rw [parisiLeftUSpatialMoment_one_zero_eq_randomFieldParisiQMoment hξ ms qs p hm hmin.1,
        ← hstat p]
    apply houter (qs p) u (parisiLeftUSpatialMoment 2 μh ξ ms qs p 0)
      (parisiLeftResponseGap μh ξ ms qs p t u) (hq p) humem hu.1 hdist
      (parisiLeftUSpatialMoment_mem_Icc ξ ms qs p hm (by decide) 0) (hc₁ p)
    have hh := abs_parisiLeftUSpatialMoment_one_sub_linear_le (μh := μh) hξ ms qs p hm hmin.1
      hgap (hscale (mapsTo_parisi_outer_variance_coordinate hξ (hmin.1.mem_Icc p) hR hu))
    rw [hM0] at hh
    rw [show -(parisiLeftResponseGap μh ξ ms qs p t u) -
      (u - qs p - parisiLeftUSpatialMoment 2 μh ξ ms qs p 0 *
        (t * (deriv ξ u - deriv ξ (qs p)))) =
      -(parisiLeftUSpatialMoment 1 μh ξ ms qs p (t * (deriv ξ u - deriv ξ (qs p))) - qs p -
        parisiLeftUSpatialMoment 2 μh ξ ms qs p 0 * (t * (deriv ξ u - deriv ξ (qs p)))) by
        dsimp only [parisiLeftResponseGap]; ring, abs_neg]
    exact hh

end SpinGlass
