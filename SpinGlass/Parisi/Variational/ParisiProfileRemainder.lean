import SpinGlass.Parisi.Minimizer.QVariation.Derivative
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform profile remainders away from zero

The profile contract (14.101) gives continuity of the second derivative on
every compact interval separated from zero. It therefore gives uniform
quadratic remainders with arbitrarily small coefficients. No uniform bound
on the third derivative, or cubic overlap remainder, is asserted here.
-/

open Set

namespace SpinGlass

/-- Compact uniform continuity of the profile curvature follows from (14.101).
The radius depends only on the profile, the separation and the requested error. -/
theorem TalagrandXiCondition.exists_uniform_second_radius
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {a η : ℝ}
    (ha : 0 < a) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Icc a 1, ∀ y ∈ Icc a 1,
      |x - y| ≤ ρ → |deriv (deriv ξ) x - deriv (deriv ξ) y| ≤ η := by
  have hc : ContinuousOn (deriv (deriv ξ)) (Icc a 1) := fun x hx =>
    (hξ.hasDeriv_second x ⟨ha.trans_le hx.1, hx.2⟩).continuousAt.continuousWithinAt
  simpa only [Real.dist_eq] using
    (Metric.uniformContinuousOn_iff_le.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hc)) η hη

/-- The profile second derivative is bounded by its value at one on a compact
positive overlap interval; no assumption at zero is used. -/
theorem TalagrandXiCondition.second_mem_Icc
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) :
    deriv (deriv ξ) x ∈ Icc (0 : ℝ) (deriv (deriv ξ) 1) :=
  ⟨(hξ.second_pos x ⟨hx.1.le, hx.2⟩ (ne_of_gt hx.1)).le,
    hξ.monotoneOn_second hx ⟨zero_lt_one, le_rfl⟩ hx.2⟩

/-- Uniform derivative-coordinate remainder on a positive overlap interval. -/
theorem abs_parisi_variance_sub_linear_le
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {u q η : ℝ}
    (hu : 0 ≤ u) (hq : q ≤ 1) (huq : u ≤ q)
    (hsecond : ∀ x ∈ Icc u q,
      |deriv (deriv ξ) x - deriv (deriv ξ) q| ≤ η) :
    |deriv ξ q - deriv ξ u - deriv (deriv ξ) q * (q - u)| ≤ η * (q - u) := by
  have hh := (convex_Icc u q).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => deriv ξ q - deriv ξ x - deriv (deriv ξ) q * (q - x))
    (f' := fun x => -deriv (deriv ξ) x + deriv (deriv ξ) q) (C := η)
    (fun x hx => (((hξ.hasDeriv_deriv x ⟨hu.trans hx.1, hx.2.trans hq⟩).const_sub
      (deriv ξ q)).sub (((hasDerivAt_id x).const_sub q).const_mul
        (deriv (deriv ξ) q))).hasDerivWithinAt.congr_deriv (by simp))
    (fun x hx => by
      rw [Real.norm_eq_abs, show -deriv (deriv ξ) x + deriv (deriv ξ) q =
        -(deriv (deriv ξ) x - deriv (deriv ξ) q) by ring, abs_neg]
      exact hsecond x hx)
    (show q ∈ Icc u q from ⟨huq, le_rfl⟩)
    (show u ∈ Icc u q from ⟨le_rfl, huq⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.2 huq)] at hh
  simpa only [sub_self, mul_zero, sub_zero, zero_sub, abs_neg, neg_sub] using hh

/-- The exact profile correction in (14.284) has a quadratic remainder with
a small coefficient controlled by the modulus of continuity of ξ''. -/
theorem abs_parisi_profile_correction_sub_quadratic_le
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {u q η : ℝ}
    (hu : 0 ≤ u) (hq : q ≤ 1) (huq : u ≤ q) (hη : 0 ≤ η)
    (hsecond : ∀ x ∈ Icc u q,
      |deriv (deriv ξ) x - deriv (deriv ξ) q| ≤ η) :
    |q * (deriv ξ q - deriv ξ u) - (parisiTheta ξ q - parisiTheta ξ u) -
      deriv (deriv ξ) q / 2 * (q - u) ^ 2| ≤ η * (q - u) ^ 2 := by
  have hh := (convex_Icc u q).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => q * (deriv ξ q - deriv ξ x) -
      (parisiTheta ξ q - parisiTheta ξ x) - deriv (deriv ξ) q / 2 * (q - x) ^ 2)
    (f' := fun x => (x - q) * (deriv (deriv ξ) x - deriv (deriv ξ) q))
    (C := η * (q - u))
    (fun x hx => by
      have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hu.trans hx.1, hx.2.trans hq⟩
      exact (((((hξ.hasDeriv_deriv x hx').const_sub (deriv ξ q)).const_mul q).sub
        ((hasDerivAt_parisiTheta (hξ.hasDeriv x hx') (hξ.hasDeriv_deriv x hx')).const_sub
          (parisiTheta ξ q))).sub
        ((((hasDerivAt_id x).const_sub q).pow 2).const_mul
          (deriv (deriv ξ) q / 2))).hasDerivWithinAt.congr_deriv (by simp; ring))
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hx.2)]
      calc
        (q - x) * |deriv (deriv ξ) x - deriv (deriv ξ) q| ≤ (q - x) * η :=
          mul_le_mul_of_nonneg_left (hsecond x hx) (sub_nonneg.2 hx.2)
        _ ≤ η * (q - u) := by nlinarith [hx.1])
    (show q ∈ Icc u q from ⟨huq, le_rfl⟩)
    (show u ∈ Icc u q from ⟨le_rfl, huq⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.2 huq)] at hh
  simpa only [sub_self, mul_zero, sub_zero, zero_sub, zero_pow (by decide : 2 ≠ 0),
    abs_neg, neg_sub, mul_assoc, pow_two] using hh

/-- Split variance is at most ξ''(1) times the overlap displacement on a
positive interval. This bound is uniform over all MIN parameters. -/
theorem parisi_variance_mem_Icc_linear
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {u q : ℝ}
    (hu : 0 < u) (hq : q ≤ 1) (huq : u ≤ q) :
    deriv ξ q - deriv ξ u ∈ Icc (0 : ℝ) (deriv (deriv ξ) 1 * (q - u)) := by
  have hh := (convex_Icc u q).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := deriv ξ) (f' := deriv (deriv ξ)) (C := deriv (deriv ξ) 1)
    (fun x hx => (hξ.hasDeriv_deriv x ⟨hu.le.trans hx.1, hx.2.trans hq⟩).hasDerivWithinAt)
    (fun x hx => by
      have hb := hξ.second_mem_Icc ⟨hu.trans_le hx.1, hx.2.trans hq⟩
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2)
    (show u ∈ Icc u q from ⟨le_rfl, huq⟩)
    (show q ∈ Icc u q from ⟨huq, le_rfl⟩)
  have hv : 0 ≤ deriv ξ q - deriv ξ u := sub_nonneg.2
    (hξ.strictMonoOn_deriv.monotoneOn ⟨hu.le, huq.trans hq⟩ ⟨hu.le.trans huq, hq⟩ huq)
  exact ⟨hv, by simpa only [Real.norm_eq_abs, abs_of_nonneg hv,
    abs_of_nonneg (sub_nonneg.2 huq)] using hh⟩

/-- Algebraic conversion of the uniform variance remainder to overlap
coordinates. The moment coefficient is bounded by one, as in the actual model. -/
theorem abs_stationary_response_sub_overlap_quadratic_le
    {f P v D B c η Δ : ℝ} (_hB : 0 ≤ B) (hη : 0 ≤ η) (hΔ : 0 ≤ Δ)
    (hv : v ∈ Icc (0 : ℝ) (B * Δ)) (hD : D ∈ Icc (0 : ℝ) B)
    (hc : c ∈ Icc (0 : ℝ) 1)
    (hresponse : |f - (P - c / 2 * v ^ 2)| ≤ 146 * v ^ 3)
    (hvariance : |v - D * Δ| ≤ η * Δ)
    (hprofile : |P - D / 2 * Δ ^ 2| ≤ η * Δ ^ 2) :
    |f - D * (1 - D * c) / 2 * Δ ^ 2| ≤
      (η * (1 + B) + 146 * B ^ 3 * Δ) * Δ ^ 2 := by
  have hsum : |v + D * Δ| ≤ 2 * B * Δ := by
    rw [abs_of_nonneg (add_nonneg hv.1 (mul_nonneg hD.1 hΔ))]
    nlinarith [hv.2, mul_le_mul_of_nonneg_right hD.2 hΔ]
  have hsquare : |v ^ 2 - D ^ 2 * Δ ^ 2| ≤ 2 * B * η * Δ ^ 2 := by
    rw [show v ^ 2 - D ^ 2 * Δ ^ 2 = (v - D * Δ) * (v + D * Δ) by ring, abs_mul]
    calc
      |v - D * Δ| * |v + D * Δ| ≤ (η * Δ) * (2 * B * Δ) :=
        mul_le_mul hvariance hsum (abs_nonneg _) (by positivity)
      _ = 2 * B * η * Δ ^ 2 := by ring
  have hcabs : |c / 2| ≤ 1 / 2 := by
    rw [abs_of_nonneg (div_nonneg hc.1 (by norm_num))]
    linarith [hc.2]
  have hmass : |c / 2 * (v ^ 2 - D ^ 2 * Δ ^ 2)| ≤ B * η * Δ ^ 2 := by
    rw [abs_mul]
    calc
      |c / 2| * |v ^ 2 - D ^ 2 * Δ ^ 2| ≤ (1 / 2) * (2 * B * η * Δ ^ 2) :=
        mul_le_mul hcabs hsquare (abs_nonneg _) (by norm_num)
      _ = B * η * Δ ^ 2 := by ring
  have hcubic : 146 * v ^ 3 ≤ 146 * B ^ 3 * Δ ^ 3 := by
    simpa only [mul_pow, mul_assoc] using mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hv.1 hv.2 3) (by norm_num : (0 : ℝ) ≤ 146)
  calc
    |f - D * (1 - D * c) / 2 * Δ ^ 2| =
        |(f - (P - c / 2 * v ^ 2)) + (P - D / 2 * Δ ^ 2) -
          c / 2 * (v ^ 2 - D ^ 2 * Δ ^ 2)| := by congr 1; ring
    _ ≤ |f - (P - c / 2 * v ^ 2)| + |P - D / 2 * Δ ^ 2| +
        |c / 2 * (v ^ 2 - D ^ 2 * Δ ^ 2)| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 146 * B ^ 3 * Δ ^ 3 + η * Δ ^ 2 + B * η * Δ ^ 2 :=
      add_le_add (add_le_add (hresponse.trans hcubic) hprofile) hmass
    _ = (η * (1 + B) + 146 * B ^ 3 * Δ) * Δ ^ 2 := by ring

/-- Uniform small quadratic remainder for a stationary response with the
actual cubic variance estimate. This replaces the rate-specific Taylor input
of (14.284) when selecting a MIN tolerance under the preserved profile contract. -/
theorem TalagrandXiCondition.exists_uniform_stationary_response_overlap_radius
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {a κ : ℝ}
    (ha : 0 < a) (hκ : 0 < κ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ Icc a 1, ∀ q ∈ Icc a 1,
      u ≤ q → q - u ≤ ρ → ∀ c ∈ Icc (0 : ℝ) 1, ∀ f : ℝ,
      |f - (q * (deriv ξ q - deriv ξ u) - (parisiTheta ξ q - parisiTheta ξ u) -
        c / 2 * (deriv ξ q - deriv ξ u) ^ 2)| ≤ 146 * (deriv ξ q - deriv ξ u) ^ 3 →
      |f - deriv (deriv ξ) q * (1 - deriv (deriv ξ) q * c) / 2 * (q - u) ^ 2| ≤
        κ * (q - u) ^ 2 := by
  let B := deriv (deriv ξ) 1
  have hB : 0 < B := hξ.second_pos 1 ⟨zero_le_one, le_rfl⟩ one_ne_zero
  let η := κ / (2 * (1 + B))
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨σ, hσ, hmod⟩ := hξ.exists_uniform_second_radius ha hη
  let ρ := min σ (κ / (292 * B ^ 3))
  refine ⟨ρ, lt_min hσ (by positivity), ?_⟩
  intro u hu q hq huq hΔ c hc f hresponse
  have hsecond : ∀ x ∈ Icc u q,
      |deriv (deriv ξ) x - deriv (deriv ξ) q| ≤ η := by
    intro x hx
    apply hmod x ⟨hu.1.trans hx.1, hx.2.trans hq.2⟩ q hq
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hx.2)]
    exact (sub_le_sub_left hx.1 q).trans (hΔ.trans (min_le_left _ _))
  have hh := abs_stationary_response_sub_overlap_quadratic_le hB.le hη.le
    (sub_nonneg.2 huq) (parisi_variance_mem_Icc_linear hξ (ha.trans_le hu.1) hq.2 huq)
    (hξ.second_mem_Icc ⟨ha.trans_le hq.1, hq.2⟩) hc hresponse
    (abs_parisi_variance_sub_linear_le hξ (ha.le.trans hu.1) hq.2 huq hsecond)
    (abs_parisi_profile_correction_sub_quadratic_le hξ (ha.le.trans hu.1) hq.2 huq
      hη.le hsecond)
  have hsmall : 292 * B ^ 3 * (q - u) ≤ κ := by
    have hh := hΔ.trans (min_le_right σ (κ / (292 * B ^ 3)))
    nlinarith [(le_div_iff₀ (by positivity : (0 : ℝ) < 292 * B ^ 3)).1 hh]
  have hηeq : η * (1 + B) = κ / 2 := by
    dsimp only [η]
    field_simp
  exact hh.trans (mul_le_mul_of_nonneg_right (by
    dsimp only [B] at hηeq hsmall ⊢
    rw [hηeq]
    nlinarith) (sq_nonneg _))

/-- Forward variance coordinates have a small linear remainder with the
profile curvature evaluated at their left endpoint. -/
theorem abs_parisi_outer_variance_sub_linear_le
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {q u η : ℝ}
    (hq : 0 ≤ q) (hu : u ≤ 1) (hqu : q ≤ u)
    (hsecond : ∀ x ∈ Icc q u,
      |deriv (deriv ξ) x - deriv (deriv ξ) q| ≤ η) :
    |deriv ξ u - deriv ξ q - deriv (deriv ξ) q * (u - q)| ≤ η * (u - q) := by
  have hh := (convex_Icc q u).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => deriv ξ x - deriv ξ q - deriv (deriv ξ) q * (x - q))
    (f' := fun x => deriv (deriv ξ) x - deriv (deriv ξ) q) (C := η)
    (fun x hx => (((hξ.hasDeriv_deriv x ⟨hq.trans hx.1, hx.2.trans hu⟩).sub_const
      (deriv ξ q)).sub (((hasDerivAt_id x).sub_const q).const_mul
        (deriv (deriv ξ) q))).hasDerivWithinAt.congr_deriv (by simp))
    (fun x hx => by rw [Real.norm_eq_abs]; exact hsecond x hx)
    (show q ∈ Icc q u from ⟨le_rfl, hqu⟩)
    (show u ∈ Icc q u from ⟨hqu, le_rfl⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hqu)] at hh
  simpa only [sub_self, mul_zero, sub_zero] using hh

/-- The mirror profile correction has a small quadratic remainder at its
left endpoint. This is the forward counterpart of (14.284), with the
opposite sign in the stationary outer response. -/
theorem abs_parisi_outer_profile_correction_sub_quadratic_le
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {q u η : ℝ}
    (hq : 0 ≤ q) (hu : u ≤ 1) (hqu : q ≤ u) (hη : 0 ≤ η)
    (hsecond : ∀ x ∈ Icc q u,
      |deriv (deriv ξ) x - deriv (deriv ξ) q| ≤ η) :
    |parisiTheta ξ u - parisiTheta ξ q - q * (deriv ξ u - deriv ξ q) -
      deriv (deriv ξ) q / 2 * (u - q) ^ 2| ≤ η * (u - q) ^ 2 := by
  have hh := (convex_Icc q u).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => parisiTheta ξ x - parisiTheta ξ q -
      q * (deriv ξ x - deriv ξ q) - deriv (deriv ξ) q / 2 * (x - q) ^ 2)
    (f' := fun x => (x - q) * (deriv (deriv ξ) x - deriv (deriv ξ) q))
    (C := η * (u - q))
    (fun x hx => by
      have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hq.trans hx.1, hx.2.trans hu⟩
      exact ((((hasDerivAt_parisiTheta (hξ.hasDeriv x hx')
        (hξ.hasDeriv_deriv x hx')).sub_const (parisiTheta ξ q)).sub
        (((hξ.hasDeriv_deriv x hx').sub_const (deriv ξ q)).const_mul q)).sub
        ((((hasDerivAt_id x).sub_const q).pow 2).const_mul
          (deriv (deriv ξ) q / 2))).hasDerivWithinAt.congr_deriv (by simp; ring))
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.2 hx.1)]
      calc
        (x - q) * |deriv (deriv ξ) x - deriv (deriv ξ) q| ≤ (x - q) * η :=
          mul_le_mul_of_nonneg_left (hsecond x hx) (sub_nonneg.2 hx.1)
        _ ≤ η * (u - q) := by nlinarith [hx.2])
    (show q ∈ Icc q u from ⟨le_rfl, hqu⟩)
    (show u ∈ Icc q u from ⟨hqu, le_rfl⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hqu)] at hh
  simpa only [sub_self, mul_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
    mul_assoc, pow_two] using hh

/-- Uniform small quadratic overlap remainder for the stationary outer
response in Section 14.9. The radius is selected before its endpoints,
moment coefficient and response value, using only the compact ξ'' modulus. -/
theorem TalagrandXiCondition.exists_uniform_stationary_outer_response_overlap_radius
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {a κ : ℝ}
    (ha : 0 < a) (hκ : 0 < κ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ Icc a 1, ∀ u ∈ Icc a 1,
      q ≤ u → u - q ≤ ρ → ∀ c ∈ Icc (0 : ℝ) 1, ∀ f : ℝ,
      |f - (q * (deriv ξ u - deriv ξ q) + c / 2 * (deriv ξ u - deriv ξ q) ^ 2 -
        (parisiTheta ξ u - parisiTheta ξ q))| ≤ 146 * (deriv ξ u - deriv ξ q) ^ 3 →
      |f - deriv (deriv ξ) q * (deriv (deriv ξ) q * c - 1) / 2 * (u - q) ^ 2| ≤
        κ * (u - q) ^ 2 := by
  let B := deriv (deriv ξ) 1
  have hB : 0 < B := hξ.second_pos 1 ⟨zero_le_one, le_rfl⟩ one_ne_zero
  let η := κ / (2 * (1 + B))
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨σ, hσ, hmod⟩ := hξ.exists_uniform_second_radius ha hη
  let ρ := min σ (κ / (292 * B ^ 3))
  refine ⟨ρ, lt_min hσ (by positivity), ?_⟩
  intro q hq u hu hqu hΔ c hc f hresponse
  have hsecond : ∀ x ∈ Icc q u,
      |deriv (deriv ξ) x - deriv (deriv ξ) q| ≤ η := by
    intro x hx
    apply hmod x ⟨hq.1.trans hx.1, hx.2.trans hu.2⟩ q hq
    rw [abs_of_nonneg (sub_nonneg.2 hx.1)]
    exact (sub_le_sub_right hx.2 q).trans (hΔ.trans (min_le_left _ _))
  have hresponse' : |-f - ((parisiTheta ξ u - parisiTheta ξ q -
      q * (deriv ξ u - deriv ξ q)) - c / 2 * (deriv ξ u - deriv ξ q) ^ 2)| ≤
      146 * (deriv ξ u - deriv ξ q) ^ 3 := by
    rw [show -f - ((parisiTheta ξ u - parisiTheta ξ q -
        q * (deriv ξ u - deriv ξ q)) - c / 2 * (deriv ξ u - deriv ξ q) ^ 2) =
        -(f - (q * (deriv ξ u - deriv ξ q) + c / 2 * (deriv ξ u - deriv ξ q) ^ 2 -
          (parisiTheta ξ u - parisiTheta ξ q))) by ring, abs_neg]
    exact hresponse
  have hh := abs_stationary_response_sub_overlap_quadratic_le hB.le hη.le
    (sub_nonneg.2 hqu) (parisi_variance_mem_Icc_linear hξ (ha.trans_le hq.1) hu.2 hqu)
    (hξ.second_mem_Icc ⟨ha.trans_le hq.1, hq.2⟩) hc hresponse'
    (abs_parisi_outer_variance_sub_linear_le hξ (ha.le.trans hq.1) hu.2 hqu hsecond)
    (abs_parisi_outer_profile_correction_sub_quadratic_le hξ (ha.le.trans hq.1) hu.2 hqu
      hη.le hsecond)
  rw [show -f - deriv (deriv ξ) q * (1 - deriv (deriv ξ) q * c) / 2 * (u - q) ^ 2 =
    -(f - deriv (deriv ξ) q * (deriv (deriv ξ) q * c - 1) / 2 * (u - q) ^ 2) by ring,
    abs_neg] at hh
  have hsmall : 292 * B ^ 3 * (u - q) ≤ κ := by
    have hh := hΔ.trans (min_le_right σ (κ / (292 * B ^ 3)))
    nlinarith [(le_div_iff₀ (by positivity : (0 : ℝ) < 292 * B ^ 3)).1 hh]
  have hηeq : η * (1 + B) = κ / 2 := by
    dsimp only [η]
    field_simp
  exact hh.trans (mul_le_mul_of_nonneg_right (by
    dsimp only [B] at hηeq hsmall ⊢
    rw [hηeq]
    nlinarith) (sq_nonneg _))

end SpinGlass
