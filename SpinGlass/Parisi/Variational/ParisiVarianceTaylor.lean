import SpinGlass.Parisi.Variational.ParisiMomentDissipation
import SpinGlass.Parisi.Variational.ParisiOuterEndpoints

/-!
# Uniform cubic variance remainders for the actual response

The first two moments give the first two derivatives of U. The uniform
variance Lipschitz bound for the second moment yields a cubic remainder
without additional regularity of the covariance profile. Conversion to an
overlap-coordinate remainder is a separate profile-calculus obligation.
-/

open MeasureTheory Set

namespace SpinGlass

/-- A moment Lipschitz bound gives a cubic response remainder on a closed
variance interval. The coefficient is sufficient for the quantitative MIN use. -/
theorem abs_response_sub_quadratic_le_of_moment_lipschitz
    {U M₁ M₂ : ℝ → ℝ} {a L v : ℝ} (hL : 0 ≤ L)
    (hU : ∀ t ∈ Icc 0 a, HasDerivWithinAt U (M₁ t) (Icc 0 a) t)
    (hM₁ : ∀ t ∈ Icc 0 a, HasDerivWithinAt M₁ (-M₂ t) (Icc 0 a) t)
    (hM₂ : ∀ t ∈ Icc 0 a, ∀ s ∈ Icc 0 a, |M₂ t - M₂ s| ≤ L * |t - s|)
    (hv : v ∈ Icc 0 a) :
    |U v - U 0 - M₁ 0 * v + M₂ 0 / 2 * v ^ 2| ≤ L * v ^ 3 := by
  have hfirst : ∀ t ∈ Icc 0 v, |M₁ t - M₁ 0 + M₂ 0 * t| ≤ L * t ^ 2 := by
    intro t ht
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 a := Icc_subset_Icc le_rfl (ht.2.trans hv.2)
    have hh := (convex_Icc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u => M₁ u - M₁ 0 + M₂ 0 * u)
      (f' := fun u => -M₂ u + M₂ 0) (C := L * t)
      (fun u hu => (((hM₁ u (hsub hu)).mono hsub).sub_const (M₁ 0)).add
        ((hasDerivWithinAt_id u _).const_mul (M₂ 0)) |>.congr_deriv (by simp))
      (fun u hu => by
        rw [Real.norm_eq_abs, show -M₂ u + M₂ 0 = -(M₂ u - M₂ 0) by ring, abs_neg]
        have hm := hM₂ u (hsub hu) 0 ⟨le_rfl, hv.1.trans hv.2⟩
        rw [sub_zero, abs_of_nonneg hu.1] at hm
        exact hm.trans (mul_le_mul_of_nonneg_left hu.2 hL))
      (show (0 : ℝ) ∈ Icc (0 : ℝ) t from ⟨le_rfl, ht.1⟩)
      (show t ∈ Icc (0 : ℝ) t from ⟨ht.1, le_rfl⟩)
    simpa only [sub_self, mul_zero, zero_add, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg ht.1, mul_assoc, pow_two] using hh
  have hsub : Icc (0 : ℝ) v ⊆ Icc 0 a := Icc_subset_Icc le_rfl hv.2
  have hh := (convex_Icc (0 : ℝ) v).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => U t - U 0 - M₁ 0 * t + M₂ 0 / 2 * t ^ 2)
    (f' := fun t => M₁ t - M₁ 0 + M₂ 0 * t) (C := L * v ^ 2)
    (fun t ht => (((((hU t (hsub ht)).mono hsub).sub_const (U 0)).sub
      ((hasDerivWithinAt_id t _).const_mul (M₁ 0))).add
      (((hasDerivWithinAt_id t _).pow 2).const_mul (M₂ 0 / 2))).congr_deriv
        (by simp only [id_eq]; ring))
    (fun t ht => by
      rw [Real.norm_eq_abs]
      exact (hfirst t ht).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ ht.1 ht.2 2) hL))
    (show (0 : ℝ) ∈ Icc (0 : ℝ) v from ⟨le_rfl, hv.1⟩)
    (show v ∈ Icc (0 : ℝ) v from ⟨hv.1, le_rfl⟩)
  simpa only [sub_self, mul_zero, zero_sub, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    add_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg hv.1,
    show L * v ^ 2 * v = L * v ^ 3 by ring] using hh

/-- The actual root U has a uniform cubic remainder in split variance.
The coefficient is independent of the level count, parameters and field law. -/
theorem abs_parisiRootU_sub_quadratic_le
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (ha : 0 < deriv ξ (qs 0) - deriv ξ 0) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) :
    |parisiRootU μh ξ ms qs v - parisiRootUSpatialMoment 1 μh ξ ms qs 0 * v +
      parisiRootUSpatialMoment 2 μh ξ ms qs 0 / 2 * v ^ 2| ≤ 146 * v ^ 3 := by
  simpa only [parisiRootU_zero, sub_zero] using
    abs_response_sub_quadratic_le_of_moment_lipschitz (by norm_num : (0 : ℝ) ≤ 146)
      (fun t ht => hasDerivWithinAt_parisiRootU (μh := μh) ξ ms qs ha ht)
      (fun t ht => hasDerivWithinAt_parisiRootUSpatialMoment_one (μh := μh) ξ ms qs ha ht)
      (fun t ht s hs => abs_parisiRootUSpatialMoment_two_sub_le ξ ms qs hm ht hs) hv

/-- The actual nonroot U has the same uniform cubic split-variance remainder,
after both the fixed prefix and the independent field/root Gaussian average. -/
theorem abs_parisiRightU_sub_quadratic_le
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) :
    |parisiRightU μh ξ ms qs p v - parisiRightUSpatialMoment 1 μh ξ ms qs p 0 * v +
      parisiRightUSpatialMoment 2 μh ξ ms qs p 0 / 2 * v ^ 2| ≤ 146 * v ^ 3 := by
  simpa only [parisiRightU_zero, sub_zero] using
    abs_response_sub_quadratic_le_of_moment_lipschitz (by norm_num : (0 : ℝ) ≤ 146)
      (fun t ht => hasDerivWithinAt_parisiRightU (μh := μh) hξ ms qs p hm hq ht)
      (fun t ht => hasDerivWithinAt_parisiRightUSpatialMoment_one (μh := μh) hξ ms qs p hm hq ht)
      (fun t ht s hs => abs_parisiRightUSpatialMoment_two_sub_le hξ ms qs p hm hq ht hs) hv

/-- Root f has a uniform cubic remainder while retaining the exact profile
correction. This does not assume boundedness of the profile's third derivative. -/
theorem abs_parisiRootf_sub_variance_quadratic_le_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) {u : ℝ} (hu : u ∈ Icc 0 (qs 0)) :
    let v := deriv ξ (qs 0) - deriv ξ u
    |parisiRootf μh ξ ms qs u - (qs 0 * v -
      parisiRootUSpatialMoment 2 μh ξ ms qs 0 / 2 * v ^ 2 -
      (parisiTheta ξ (qs 0) - parisiTheta ξ u))| ≤ 146 * v ^ 3 := by
  have hqpos := randomFieldParisiQ_first_pos_of_isMin ms qs hμ.integrable_id hm hξ hμ hmin
  have ha := sub_pos.2 (hξ.strictMonoOn_deriv ⟨le_rfl, zero_le_one⟩ (hmin.1.mem_Icc 0) hqpos)
  have hMq : parisiRootUSpatialMoment 1 μh ξ ms qs 0 = qs 0 := by
    rw [parisiRootUSpatialMoment_one_zero_eq_randomFieldParisiQMoment μh ξ ms qs hm]
    exact ((randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
      ms qs hm hξ hμ hmin).2 0).symm
  have hrem := abs_parisiRootU_sub_quadratic_le (μh := μh) ξ ms qs hm ha
    (mapsTo_parisiRoot_variance_coordinate hξ (hmin.1.mem_Icc 0) hu)
  rw [hMq] at hrem
  convert! hrem using 1
  congr 1
  dsimp only [parisiRootf]
  ring

/-- Nonroot f has the same uniform variance remainder after stationarity,
with its exact overlap-dependent profile correction. -/
theorem abs_parisiRightf_sub_variance_quadratic_le_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) {u : ℝ}
    (hu : u ∈ Icc (qs p.castSucc) (qs p.succ)) :
    let v := deriv ξ (qs p.succ) - deriv ξ u
    |parisiRightf μh ξ ms qs p u - (qs p.succ * v -
      parisiRightUSpatialMoment 2 μh ξ ms qs p 0 / 2 * v ^ 2 -
      (parisiTheta ξ (qs p.succ) - parisiTheta ξ u))| ≤ 146 * v ^ 3 := by
  have hMq : parisiRightUSpatialMoment 1 μh ξ ms qs p 0 = qs p.succ := by
    rw [parisiRightUSpatialMoment_one_zero_eq_randomFieldParisiQMoment hξ ms qs p hm hmin.1]
    exact ((randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
      ms qs hm hξ hμ hmin).2 p.succ).symm
  have hrem := abs_parisiRightU_sub_quadratic_le (μh := μh) hξ ms qs p hm hmin.1
    (mapsTo_parisi_variance_coordinate hξ (hmin.1.mem_Icc p.castSucc)
      (hmin.1.mem_Icc p.succ) hu)
  rw [hMq] at hrem
  convert! hrem using 1
  congr 1
  dsimp only [parisiRightf]
  ring

/-- The actual outer response has the mirror cubic variance remainder.
Its quadratic term has positive sign because the initial moment increases
with outer variance. The coefficient remains independent of all MIN data. -/
theorem abs_parisiLeftU_sub_quadratic_le
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hgap : qs p < qExt qs (p.val + 2)) {w : ℝ}
    (hw : w ∈ Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) :
    |parisiLeftU μh ξ ms qs p w - parisiLeftUSpatialMoment 1 μh ξ ms qs p 0 * w -
      parisiLeftUSpatialMoment 2 μh ξ ms qs p 0 / 2 * w ^ 2| ≤ 146 * w ^ 3 := by
  have hh := abs_response_sub_quadratic_le_of_moment_lipschitz
    (U := parisiLeftU μh ξ ms qs p) (M₁ := parisiLeftUSpatialMoment 1 μh ξ ms qs p)
    (M₂ := fun t => -parisiLeftUSpatialMoment 2 μh ξ ms qs p t)
    (by norm_num : (0 : ℝ) ≤ 146)
    (fun t ht => hasDerivWithinAt_parisiLeftU (μh := μh) hξ ms qs p hm hq hgap ht)
    (fun t ht => by simpa only [neg_neg] using
      hasDerivWithinAt_parisiLeftUSpatialMoment_one (μh := μh) hξ ms qs p hm hq hgap ht)
    (fun t ht s hs => by simpa only [neg_sub_neg, abs_sub_comm] using
      abs_parisiLeftUSpatialMoment_two_sub_le (μh := μh) hξ ms qs p hm hq hgap ht hs) hw
  rw [parisiLeftU_zero, sub_zero] at hh
  convert! hh using 1
  congr 1
  ring

/-- The stationary outer f retains its exact profile correction and has
the uniform cubic variance error. The terminal split and k=0 are included. -/
theorem abs_parisiLeftf_sub_variance_quadratic_le_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) {u : ℝ}
    (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) :
    let w := deriv ξ u - deriv ξ (qs p)
    |parisiLeftf μh ξ ms qs p u - (qs p * w +
      parisiLeftUSpatialMoment 2 μh ξ ms qs p 0 / 2 * w ^ 2 -
      (parisiTheta ξ u - parisiTheta ξ (qs p)))| ≤ 146 * w ^ 3 := by
  have hgap := parisi_outer_overlap_gap_of_isMin ms qs p hm hξ hμ hmin
  have hMq : parisiLeftUSpatialMoment 1 μh ξ ms qs p 0 = qs p := by
    rw [parisiLeftUSpatialMoment_one_zero_eq_randomFieldParisiQMoment hξ ms qs p hm hmin.1]
    exact ((randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
      ms qs hm hξ hμ hmin).2 p).symm
  have hh := abs_parisiLeftU_sub_quadratic_le (μh := μh) hξ ms qs p hm hmin.1 hgap
    (mapsTo_parisi_outer_variance_coordinate hξ (hmin.1.mem_Icc p)
      (qExt_mem_Icc hmin.1.monotone hmin.1.2.1 hmin.1.2.2 _) hu)
  rw [hMq] at hh
  convert! hh using 1
  congr 1
  dsimp only [parisiLeftf]
  ring

end SpinGlass
