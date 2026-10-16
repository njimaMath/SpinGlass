import Common.Mathlib.Probability.PointProcess.CascadeTilt

/-!
# The actual weighted cascade product and constrained recursion

The cascade tilt is the normalized product of the actual layer weights.
For a terminal factor between zero and one, its expectation is bounded
by the constrained-to-unconstrained recursion ratio raised to the first
mass. This is the multiplicative form of Talagrand's (14.120).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SpinGlass

noncomputable def parisiCascadeFirstMass : (k : ℕ) → (Fin k → ℝ) → ℝ
  | 0, _ => 1
  | _ + 1, ms => ms 0

/-- The normalized weighted product bound for a concrete finite
cascade. All weights and recursions are the existing integral definitions;
no logarithmic pressure comparison is supplied as a hypothesis. -/
theorem cascadeTilt_le_constrained_ratio {T : Type*} [MeasurableSpace T] (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {G A : (Fin k → T) → ℝ≥0∞}, Measurable G → Measurable A →
      (∀ z, 0 < G z) → Monotone ms → (∀ i, 0 < ms i) → (∀ i, ms i ≤ 1) →
      (∀ z, A z ≤ 1) → (∫⁻ z, G z ∂Measure.pi μs) ≠ ∞ →
      cascadeTilt k ms μs G A ≤
        (cascadeRec k ms μs (fun z => G z * A z) / cascadeRec k ms μs G) ^
          parisiCascadeFirstMass k ms := by
  induction k with
  | zero =>
    intro ms μs _ G A hG hA hGp hmono hpos hle hA1 hfin
    have hG0 : G Fin.elim0 ≠ ∞ := by
      rw [Measure.pi_of_empty, lintegral_dirac' _ hG] at hfin
      exact fun h => hfin (by rw [← h]; exact congrArg G (Subsingleton.elim _ _))
    simp only [cascadeTilt_zero, cascadeRec_zero, parisiCascadeFirstMass, ENNReal.rpow_one]
    rw [mul_comm, ENNReal.mul_div_cancel_right (hGp Fin.elim0).ne' hG0]
  | succ k ih =>
    intro ms μs _ G A hG hA hGp hmono hpos hle hA1 hfin
    let RG := cascadeRec (k + 1) ms μs G
    let H := fun z : Fin (k + 1) → T => G z * A z
    have hH : Measurable H := hG.mul hA
    have hRG (z : T) : 0 < cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) :=
      cascadeRec_pos k _ _ (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hGp _) (fun i => hpos i.succ)
    have hmass : ms 0 ≤ parisiCascadeFirstMass k (Fin.tail ms) := by
      cases k with
      | zero => exact hle 0
      | succ n => exact hmono (Fin.zero_le (1 : Fin (n + 2)))
    have hpoint : ∀ᵐ z ∂μs 0,
        cascadeW k ms μs G z * cascadeTilt k (Fin.tail ms) (Fin.tail μs)
          (fun zs => G (Fin.cons z zs)) (fun zs => A (Fin.cons z zs)) ≤
        cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => H (Fin.cons z zs)) ^ ms 0 / RG ^ ms 0 := by
      filter_upwards [ae_lintegral_pi_cons_ne_top k μs hG hfin] with z hz
      let R := cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
      let S := cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => H (Fin.cons z zs))
      have hRfin : R ≠ ∞ := cascadeRec_ne_top k _ _
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun i => hpos i.succ) (fun i => hle i.succ) hz
      have hSR : S ≤ R := cascadeRec_mono k _ _ (fun zs => by
        dsimp only [H]
        simpa only [mul_one] using mul_le_mul_right (hA1 (Fin.cons z zs)) (G (Fin.cons z zs)))
        (fun i => (hpos i.succ).le)
      have hratio : S / R ≤ 1 := ENNReal.div_le_of_le_mul (by simpa only [one_mul] using hSR)
      have ht := ih (Fin.tail ms) (Fin.tail μs)
        (G := fun zs => G (Fin.cons z zs)) (A := fun zs => A (Fin.cons z zs))
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (hA.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hGp _) (fun _ _ hij => hmono (Fin.succ_le_succ_iff.2 hij))
        (fun i => hpos i.succ) (fun i => hle i.succ) (fun zs => hA1 _) hz
      have htail : cascadeTilt k (Fin.tail ms) (Fin.tail μs)
          (fun zs => G (Fin.cons z zs)) (fun zs => A (Fin.cons z zs)) ≤ (S / R) ^ ms 0 :=
        ht.trans (ENNReal.rpow_le_rpow_of_exponent_ge hratio hmass)
      have he : R / RG * (S / R) = S / RG := by
        calc
          _ = (R * (S / R)) / RG := by simp only [div_eq_mul_inv]; ac_rfl
          _ = _ := by rw [ENNReal.mul_div_cancel (hRG z).ne' hRfin]
      calc
        _ ≤ cascadeW k ms μs G z * (S / R) ^ ms 0 := mul_le_mul_right htail _
        _ = S ^ ms 0 / RG ^ ms 0 := by
          change (R / RG) ^ ms 0 * (S / R) ^ ms 0 = _
          rw [← ENNReal.mul_rpow_of_nonneg _ _ (hpos 0).le, he,
            ENNReal.div_rpow_of_nonneg _ _ (hpos 0).le]
    calc
      _ ≤ ∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => H (Fin.cons z zs)) ^ ms 0 /
          RG ^ ms 0 ∂μs 0 := lintegral_mono_ae hpoint
      _ = (cascadeRec (k + 1) ms μs H / RG) ^ ms 0 := by
        rw [ENNReal.div_rpow_of_nonneg _ _ (hpos 0).le,
          cascadeRec_rpow_eq_lintegral k ms μs H (hpos 0)]
        simp_rw [div_eq_mul_inv]
        exact lintegral_mul_const _ ((measurable_cascadeRec_cons k _ _ hH).pow_const _)

end SpinGlass
