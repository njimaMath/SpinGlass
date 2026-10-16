import SpinGlass.Parisi.Coupled.CoupledInnerFreeSite
import SpinGlass.Parisi.Coupled.CoupledInnerFreeCorrection

/-!
# The actual zero-coupling comparison bound as a mass family

At the matching mass this family equals twice the original interpolation
bracket. Its derivative is the concrete U-response minus the time-scaled
inner theta increment, as in Talagrand's (14.335).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

noncomputable def parisiInnerFreeScalarBound (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (t u b : ℝ) : ℝ :=
  2 * Real.log 2 + 2 * parisiInnerFreeZeroValue μh ξ ms qs p (t * (deriv ξ (qs p.succ) - deriv ξ u)) b -
    t * (parisiCorrection ξ ms qs + (b - ms p) * (parisiTheta ξ (qs p.succ) - parisiTheta ξ u)) -
    parisiAuxTerminalVar ξ qs t

/-- The free-mass scalar bound at the original mass is exactly twice
the unchanged interpolation bracket. -/
theorem parisiInnerFreeScalarBound_matching {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (hq : ParisiQAdmissible qs)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p.castSucc) (qs p.succ)) :
    parisiInnerFreeScalarBound μh ξ ms qs p t u (ms p) = 2 * parisiInterpolationBracket μh ξ ms qs t := by
  have hsplit := mapsTo_parisi_variance_coordinate hξ (hq.mem_Icc p.castSucc) (hq.mem_Icc p.succ) hu
  have hv : t * (deriv ξ (qs p.succ) - deriv ξ u) ∈
      Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)) :=
    ⟨mul_nonneg ht.1 hsplit.1, by nlinarith [mul_nonneg (sub_nonneg.2 ht.2) hsplit.1, hsplit.2]⟩
  unfold parisiInnerFreeScalarBound
  rw [parisiInnerFreeZeroValue_matching hμ ξ ms qs p hv]
  simp only [sub_self, zero_mul, add_zero]
  unfold parisiInterpolationBracket parisiSplitBracket
  ring

/-- The actual mass derivative in (14.335), after the external-field
average, correction and terminal normalization. -/
theorem hasDerivAt_parisiInnerFreeScalarBound_matching {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p.castSucc) (qs p.succ)) :
    HasDerivAt (parisiInnerFreeScalarBound μh ξ ms qs p t u)
      (parisiRightU μh ξ ms qs p (t * (deriv ξ (qs p.succ) - deriv ξ u)) -
        t * (parisiTheta ξ (qs p.succ) - parisiTheta ξ u)) (ms p) := by
  have hsplit := mapsTo_parisi_variance_coordinate hξ (hq.mem_Icc p.castSucc) (hq.mem_Icc p.succ) hu
  have hv : t * (deriv ξ (qs p.succ) - deriv ξ u) ∈
      Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)) :=
    ⟨mul_nonneg ht.1 hsplit.1, by nlinarith [mul_nonneg (sub_nonneg.2 ht.2) hsplit.1, hsplit.2]⟩
  have hd := hasDerivAt_parisiInnerFreeZeroValue_matching hμ ξ ms qs p hm hv
  have hc := ((((hasDerivAt_id (ms p)).sub_const (ms p)).mul_const
    (parisiTheta ξ (qs p.succ) - parisiTheta ξ u)).const_add (parisiCorrection ξ ms qs)).const_mul t
  unfold parisiInnerFreeScalarBound
  convert! (((hd.const_mul 2).const_add (2 * Real.log 2)).sub hc).sub_const
    (parisiAuxTerminalVar ξ qs t : ℝ) using 1
  ring

end SpinGlass
