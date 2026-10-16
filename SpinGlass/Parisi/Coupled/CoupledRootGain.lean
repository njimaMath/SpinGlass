import SpinGlass.Parisi.Coupled.CoupledRootMassLimit

/-!
# Positive root insertions and the limiting one-site gain

The actual coupled one-site value, zero-coupling slope and Taylor gain
are identified with the root mass family. Its value and slope limits
were proved in CoupledRootMassLimit and do not assume a mass-zero cascade
comparison theorem.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal BigOperators

namespace SpinGlass

noncomputable def parisiRootCouplingValue (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (v m lam : ℝ) : ℝ :=
  randomFieldPairSiteY₀ μh (parisiRootResponseMasses ms m)
    (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal (parisiRootResponseVars ξ qs v)
    lam (couplingFactorSgn 1 1 0) (fun i => couplingFactorSgn 1 1 (i.val + 1))

/-- Root conditional-square averaging uses the same independent
field/Gaussian product law as the concrete mass-limit moment. -/
theorem integral_cascadeTiltTanhSq_parisi_root_eq {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (v : ℝ) :
    (∫ h, ∫ z, cascadeTiltTanhSq (parisiRootResponseMasses ms m)
      (parisiRootResponseVars ξ qs v) 0 (h + z)
      ∂gaussianReal 0 (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal ∂μh) =
      parisiRootCouplingMoment μh ξ ms qs v m := by
  rw [integral_cascadeTiltTanhSq_externalField_prod _ _
    (parisiRootResponseMasses_pos ms hm hm0) (parisiRootResponseMasses_le_one ms hm hm1) 0 (by omega)]
  unfold parisiRootCouplingMoment
  exact integral_congr_ae (.of_forall fun hz =>
    cascadeTiltTanhSq_parisi_root_eq ξ ms qs hm hm0 hm1 v (hz.1 + hz.2))

/-- The half zero-coupling value is the actual averaged positive-mass
root layer, with first-moment integrability proved before Fubini. -/
theorem integral_logCoshRec_parisi_root_eq {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m) (v : ℝ) :
    (∫ h, ∫ z, logCoshRec (k + 2) (parisiRootResponseMasses ms m)
      (parisiRootResponseVars ξ qs v) (h + z)
      ∂gaussianReal 0 (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal ∂μh) =
      parisiRootCouplingZeroValue μh ξ ms qs v m := by
  let w := (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal
  have hzg : HasLinearGrowth id := ⟨0, 1, zero_le_one, by simp⟩
  have hz : Integrable id (gaussianReal 0 w) :=
    hzg.toHasExpGrowth.integrable_gaussianReal measurable_id.aestronglyMeasurable
  have hH : Integrable (fun hz : ℝ × ℝ => hz.1 + hz.2) (μh.prod (gaussianReal 0 w)) :=
    (hμ.comp_fst _).add (hz.comp_snd _)
  have hi := integrable_coleHopf_comp_shift (H := fun hz : ℝ × ℝ => hz.1 + hz.2)
    (measurable_fst.add measurable_snd) hH
    (parisiRootSuffix_spatial_regular_four ξ ms qs).1.continuous.measurable
    (abs_parisiRootSuffix_sub_le ξ ms qs) m v.toNNReal
  simp_rw [logCoshRec_eq_coleHopfIterate_terminal_zero _ _ (parisiRootResponseMasses_pos ms hm hm0)]
  simp only [parisiRootResponseMasses, parisiRootResponseVars, coleHopfIterate_succ,
    Fin.cons_zero, Fin.tail_cons]
  change (∫ h, ∫ z, coleHopf m v.toNNReal (parisiRootSuffix ξ ms qs) (h + z)
    ∂gaussianReal 0 w ∂μh) = _
  unfold parisiRootCouplingZeroValue
  exact (integral_prod _ hi).symm

theorem parisiRootCouplingValue_zero {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m) (v : ℝ) :
    parisiRootCouplingValue μh ξ ms qs v m 0 = 2 * parisiRootCouplingZeroValue μh ξ ms qs v m := by
  have hp (h : ℝ) : pairSiteY₀ (parisiRootResponseMasses ms m)
      (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal (parisiRootResponseVars ξ qs v) 0
      (fun _ => h) (couplingFactorSgn 1 1 0) (fun i => couplingFactorSgn 1 1 (i.val + 1)) =
        2 * ∫ z, logCoshRec (k + 2) (parisiRootResponseMasses ms m)
          (parisiRootResponseVars ξ qs v) (h + z)
          ∂gaussianReal 0 (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal := by
    simpa only [Nat.sub_self, halveBelow_zero] using pairSiteY₀_coupling_zero
      (parisiRootResponseMasses ms m) (parisiRootResponseMasses_pos ms hm hm0)
      (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal (parisiRootResponseVars ξ qs v) h
      (τ := 1) (by norm_num)
  unfold parisiRootCouplingValue randomFieldPairSiteY₀
  simp_rw [hp]
  rw [integral_const_mul, integral_logCoshRec_parisi_root_eq hμ ξ ms qs hm hm0 v]

theorem hasDerivAt_parisiRootCouplingValue_zero {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (v : ℝ) :
    HasDerivAt (parisiRootCouplingValue μh ξ ms qs v m)
      (parisiRootCouplingMoment μh ξ ms qs v m) 0 := by
  have hd := hasDerivAt_randomFieldPairSiteY₀_coupling_zero hμ
    (parisiRootResponseMasses ms m) (parisiRootResponseMasses_pos ms hm hm0)
    (parisiRootResponseMasses_le_one ms hm hm1)
    (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal (parisiRootResponseVars ξ qs v)
    (τ := 1) (by norm_num)
  simp only [Nat.sub_self, halveBelow_zero] at hd
  rw [integral_cascadeTiltTanhSq_parisi_root_eq ξ ms qs hm hm0 hm1 v] at hd
  exact hd

/-- The positive insertion yields the actual one-site coupling gain
whose value and slope have proved zero-mass limits. -/
theorem parisiRootCouplingValue_le_gain {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m) (hmr : m ≤ mExt ms 1) (v u : ℝ) :
    let β := parisiRootCouplingMoment μh ξ ms qs v m - u
    parisiRootCouplingValue μh ξ ms qs v m (-β) + β * u ≤
      2 * parisiRootCouplingZeroValue μh ξ ms qs v m - β ^ 2 / 2 := by
  have hm1 : m ≤ 1 := hmr.trans (mExt_le_one (fun i => (hm.2.2 i).le) _)
  have hb := randomFieldPairSiteY₀_coupling_zero_le_gain hμ
    (parisiRootResponseMasses ms m) (parisiRootResponseMasses_monotone ms hm hmr)
    (parisiRootResponseMasses_pos ms hm hm0) (parisiRootResponseMasses_le_one ms hm hm1)
    (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal (parisiRootResponseVars ξ qs v)
    (τ := 1) (by norm_num) u
  dsimp only at hb ⊢
  simp only [Nat.sub_self, halveBelow_zero] at hb
  rw [integral_cascadeTiltTanhSq_parisi_root_eq ξ ms qs hm hm0 hm1 v,
    integral_logCoshRec_parisi_root_eq hμ ξ ms qs hm hm0 v] at hb
  exact hb

end SpinGlass
