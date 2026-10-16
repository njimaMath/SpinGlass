import SpinGlass.Parisi.Coupled.CoupledOuterFreeSite
import SpinGlass.Parisi.Coupled.CoupledOuterFreeCorrection

/-!
# The actual zero-coupling outer mass family

The matching value is twice the original interpolation bracket.
Its mass derivative is the concrete outer U-response minus the
time-scaled outer theta increment, including the terminal old mass one.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

noncomputable def parisiOuterFreeScalarBound (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t u b : ℝ) : ℝ :=
  2 * Real.log 2 + 2 * parisiOuterFreeZeroValue μh ξ ms qs p (t * (deriv ξ u - deriv ξ (qs p))) b -
    t * (parisiCorrection ξ ms qs + (b - mExt ms (p.val + 1)) * (parisiTheta ξ u - parisiTheta ξ (qs p))) -
    parisiAuxTerminalVar ξ qs t

theorem parisiOuterFreeScalarBound_matching {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (hq : ParisiQAdmissible qs)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) :
    parisiOuterFreeScalarBound μh ξ ms qs p t u (mExt ms (p.val + 1)) =
      2 * parisiInterpolationBracket μh ξ ms qs t := by
  unfold parisiOuterFreeScalarBound
  rw [parisiOuterFreeZeroValue_matching hμ ξ ms qs p (parisi_outer_time_variance_mem_Icc hξ qs p hq ht hu)]
  simp only [sub_self, zero_mul, add_zero]
  unfold parisiInterpolationBracket parisiSplitBracket
  ring

theorem hasDerivAt_parisiOuterFreeScalarBound_matching {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) :
    HasDerivAt (parisiOuterFreeScalarBound μh ξ ms qs p t u)
      (parisiLeftU μh ξ ms qs p (t * (deriv ξ u - deriv ξ (qs p))) -
        t * (parisiTheta ξ u - parisiTheta ξ (qs p))) (mExt ms (p.val + 1)) := by
  have hd := hasDerivAt_parisiOuterFreeZeroValue_matching hμ ξ ms qs p hm
    (parisi_outer_time_variance_mem_Icc hξ qs p hq ht hu)
  have hc := ((((hasDerivAt_id (mExt ms (p.val + 1))).sub_const (mExt ms (p.val + 1))).mul_const
    (parisiTheta ξ u - parisiTheta ξ (qs p))).const_add (parisiCorrection ξ ms qs)).const_mul t
  unfold parisiOuterFreeScalarBound
  convert! (((hd.const_mul 2).const_add (2 * Real.log 2)).sub hc).sub_const
    (parisiAuxTerminalVar ξ qs t : ℝ) using 1
  ring

end SpinGlass
