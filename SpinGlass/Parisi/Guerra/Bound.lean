import SpinGlass.Parisi.Guerra.Overlap

/-!
# Bound

The finite-volume Guerra upper bound.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

/-! ### Abel summation and Guerra's bound -/

/-- Guerra's broken replica-symmetry bound (Talagrand Vol. II, Theorem 14.4.3, (14.90)):
for a convex `ξ` with `ξ'(0) = 0`, a nondecreasing `0 = q₀ ≤ q₁ ≤ ⋯ ≤ q_{k+1} ≤ q_{k+2} = 1`
along which `ξ'` is nondecreasing, and `0 < m₁ < ⋯ < m_k < 1`,

`p_N(hVec) ≤ (1/N) ∑ᵢ 𝒫_k(m, q; hᵢ)`, conditional on the realized site fields. -/
theorem siteFieldMixedPSpinFreeEnergy_le_parisiFunctional (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (qs : Fin (k + 1) → ℝ) (ms : Fin k → ℝ)
    (h0 : deriv ξ 0 = 0)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (hq01 : ∀ r, qExt qs r ∈ Set.Icc (0 : ℝ) 1)
    (htan : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1, ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) (h : Fin N → ℝ) :
    siteFieldMixedPSpinFreeEnergy N ξ h ≤ (1 / (N : ℝ)) * ∑ i, parisiFunctional ξ (h i) ms qs := by
  set v₀ : ℝ≥0 := parisiVar ξ qs 0 with hv₀
  set vs : Fin k → ℝ≥0 := fun p => parisiVar ξ qs (p.val + 1) with hvs
  set Pw := cascadeWeightsLaw k ms with hPw
  set Pm := marksLaw N k v₀ vs with hPm
  set Φ : CascadeWeights k → ℝ := fun w =>
    (1 / (N : ℝ)) * ∫ z, logRatio N k h (w, z) ∂Pm with hΦ
  set Ψ : CascadeWeights k → ℝ := fun w => ∫ t in (0 : ℝ)..1, guerraBound N k ξ qs h w t with hΨ
  -- integrability of the two terms
  have hF := integrable_logRatio N k ms hsm hpos hlt v₀ vs h
  have hintΦ : Integrable Φ Pw := (hF.integral_prod_left).const_mul _
  have hintΨ : Integrable Ψ Pw := by
    have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    have hswap : Integrable (Function.uncurry fun (w : CascadeWeights k) (t : ℝ) =>
        guerraBound N k ξ qs h w t) (Pw.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
      Integrable.of_bound (measurable_guerraBound N k ξ qs h).aestronglyMeasurable
        ((1 / 2) * |ξ 1 - deriv ξ (qs (Fin.last k))|
          + (1 / 2) * ∑ r ∈ Finset.range (k + 1), |parisiTheta ξ (qExt qs (r + 1))|)
        (Filter.Eventually.of_forall fun q => by
          rw [Real.norm_eq_abs]; exact abs_guerraBound_le N k ξ qs h q.1 q.2)
    have hIP := hswap.integral_prod_left
    refine hIP.congr (Filter.Eventually.of_forall fun w => ?_)
    change (∫ y in Set.Ioc (0 : ℝ) 1, guerraBound N k ξ qs h w y)
      = ∫ t in (0 : ℝ)..1, guerraBound N k ξ qs h w t
    exact (intervalIntegral.integral_of_le (zero_le_one' ℝ)).symm
  -- the fixed-weights bound, almost surely in the weights
  have hae : ∀ᵐ w ∂Pw, siteFieldMixedPSpinFreeEnergy N ξ h ≤ Φ w + Ψ w := by
    filter_upwards [ae_weightSum_ne_zero_ne_top k ms hsm hpos hlt] with w hw
    exact guerra_fixed_weights N k hN ξ hS qs h0 hmono hq01 htan h w hw.1 hw.2
  have hle : siteFieldMixedPSpinFreeEnergy N ξ h ≤ (∫ w, Φ w ∂Pw) + ∫ w, Ψ w ∂Pw := by
    have h1 := integral_mono_ae (integrable_const (siteFieldMixedPSpinFreeEnergy N ξ h))
      (hintΦ.add hintΨ) hae
    rw [integral_const, probReal_univ, one_smul] at h1
    calc siteFieldMixedPSpinFreeEnergy N ξ h ≤ ∫ w, (Φ + Ψ) w ∂Pw := h1
      _ = (∫ w, Φ w ∂Pw) + ∫ w, Ψ w ∂Pw := integral_add hintΦ hintΨ
  -- the first term: `φ(0)`
  have hΦint : (∫ w, Φ w ∂Pw)
      = Real.log 2 + (1 / (N : ℝ)) * ∑ i,
          (parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h i + x)))
            - (parisiVar ξ qs (k + 1) : ℝ) / 2) := by
    rw [hΦ, integral_const_mul, integral_prod _ hF |>.symm,
      integral_logRatio_eq N k ξ ms hsm hpos hlt qs h, mul_add,
      ← mul_assoc, one_div, inv_mul_cancel₀ (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0),
      one_mul]
  -- the second term: the averaged bound
  have hΨint : (∫ w, Ψ w ∂Pw)
      = (1 / 2) * (ξ 1 - deriv ξ (qs (Fin.last k)))
        + (1 / 2) * ∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1))
            * (mExt ms (r + 1) - mExt ms r) :=
    integral_intervalIntegral_guerraBound N k ξ qs h ms hsm hpos hlt
  rw [hΦint, hΨint] at hle
  refine hle.trans (le_of_eq ?_)
  -- Talagrand's second form (14.403) of the functional
  have hqlast : qExt qs (k + 1) = qs (Fin.last k) := qExt_succ_of_lt qs (Nat.lt_succ_self k)
  have hqtop : qExt qs (k + 1 + 1) = 1 := qExt_of_le qs (by omega)
  have hv : (parisiVar ξ qs (k + 1) : ℝ) = deriv ξ 1 - deriv ξ (qs (Fin.last k)) := by
    have hnn : (0 : ℝ) ≤ deriv ξ (qExt qs (k + 1 + 1)) - deriv ξ (qExt qs (k + 1)) := by
      have := hmono (k + 1) (le_refl (k + 1))
      linarith
    rw [parisiVar, Real.coe_toNNReal _ hnn, hqtop, hqlast]
  simp_rw [parisiFunctional_eq_theta_sum ξ, hv, parisiTheta]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne']
  <;> ring

/-- The constant-field bound is the specialization to a constant site vector. -/
theorem mixedPSpinFreeEnergy_le_parisiFunctional (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (qs : Fin (k + 1) → ℝ) (ms : Fin k → ℝ)
    (h0 : deriv ξ 0 = 0)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (hq01 : ∀ r, qExt qs r ∈ Set.Icc (0 : ℝ) 1)
    (htan : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) (h : ℝ) :
    mixedPSpinFreeEnergy N ξ h ≤ parisiFunctional ξ h ms qs := by
  have hb := siteFieldMixedPSpinFreeEnergy_le_parisiFunctional N k hN ξ hS qs ms h0
    hmono hq01 htan hsm hpos hlt (fun _ => h)
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, one_div, inv_mul_cancel₀ (show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne')]
    using hb

/-- Guerra's broken replica-symmetry bound under Talagrand's own hypotheses
(Vol. II, Theorem 14.4.3): for a convex differentiable `ξ` with `ξ'(0) = 0`, a nondecreasing
`q₁ ≤ ⋯ ≤ q_{k+1}` in `[0, 1]` and `0 < m₁ < ⋯ < m_k < 1`, `p_N ≤ 𝒫_k(m, q)`. -/
theorem mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (hconv : ConvexOn ℝ Set.univ ξ)
    (hdiff : Differentiable ℝ ξ) (h0 : deriv ξ 0 = 0) (qs : Fin (k + 1) → ℝ)
    (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0) (hq1 : qs (Fin.last k) ≤ 1) (ms : Fin k → ℝ)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) (h : ℝ) :
    mixedPSpinFreeEnergy N ξ h ≤ parisiFunctional ξ h ms qs := by
  have hderiv : Monotone (deriv ξ) :=
    monotoneOn_univ.1 (hconv.monotoneOn_deriv fun x _ => hdiff x)
  refine mixedPSpinFreeEnergy_le_parisiFunctional N k hN ξ hS qs ms h0
    (fun r hr => hderiv (qExt_le_succ hqmono hq0 hq1 hr))
    (fun r => qExt_mem_Icc hqmono hq0 hq1 r) (fun x _ q _ => ?_) hsm hpos hlt h
  rw [mul_comm (x - q) (deriv ξ q)]
  exact hconv.add_deriv_mul_sub_le_univ hdiff q x

/-- Guerra's bound for the Sherrington–Kirkpatrick model at every level `k`: for
`0 ≤ q₁ ≤ ⋯ ≤ q_{k+1} ≤ 1` and `0 < m₁ < ⋯ < m_k < 1`,
`p_N(β, h) ≤ 𝒫_k(m, q)` for the profile `ξ(x) = β²x²/2`. At `k = 0` this is the
replica-symmetric bound of Vol. I, Theorem 1.3.7. -/
theorem skFreeEnergy_le_parisiFunctional (hN : 0 < N) (β h : ℝ) (qs : Fin (k + 1) → ℝ)
    (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0) (hq1 : qs (Fin.last k) ≤ 1) (ms : Fin k → ℝ)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) :
    skFreeEnergy N β h ≤ parisiFunctional (skCovXi β) h ms qs := by
  change mixedPSpinFreeEnergy N (skCovXi β) h ≤ _
  exact mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn N k hN (skCovXi β)
    (posSemidef_skCovMatrix N β) (convexOn_univ_skCovXi β) (differentiable_skCovXi β)
    (deriv_skCovXi_zero β) qs hqmono hq0 hq1 ms hsm hpos hlt h

/-- The replica-symmetric bound at finite `N` is the case `k = 0` of Guerra's bound: for
`0 ≤ q ≤ 1`, `p_N(β, h) ≤ 𝔼 log (2 cosh (β √q z + h)) + β²(1-q)²/4`. This is Vol. I,
Theorem 1.3.7 (there stated in the limit). -/
theorem skFreeEnergy_le_rs_bound (hN : 0 < N) (β h q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    skFreeEnergy N β h
      ≤ (∫ z : ℝ, Real.log (2 * Real.cosh (β * Real.sqrt q * z + h)) ∂gaussianReal 0 1)
        + β ^ 2 / 4 * (1 - q) ^ 2 := by
  have hmono1 : Monotone (![q] : Fin (0 + 1) → ℝ) := by
    intro a b _
    fin_cases a
    fin_cases b
    simp
  have hsm0 : StrictMono (![] : Fin 0 → ℝ) := fun a _ _ => a.elim0
  have hmain := skFreeEnergy_le_parisiFunctional N 0 hN β h ![q] hmono1
    (by simpa using hq0) (by simpa using hq1) ![] hsm0 (fun i => i.elim0) (fun i => i.elim0)
  rwa [parisiFunctional_skCovXi_zero β h q hq0 hq1] at hmain


end

end SpinGlass
