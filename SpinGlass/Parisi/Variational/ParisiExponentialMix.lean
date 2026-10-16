import SpinGlass.Parisi.Variational.ParisiParameterContinuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Normalized exponential comparison and its equality case

Convexity of the exponential gives the normalized form of the
Holder inequality used in the Cole-Hopf rearrangement. Strict convexity
identifies equality with agreement of the normalized logarithmic tilts.
-/

open MeasureTheory ProbabilityTheory Set

namespace SpinGlass

theorem exp_convex_mix_le {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (f g : ℝ) :
    Real.exp (a * f + (1 - a) * g) ≤ a * Real.exp f + (1 - a) * Real.exp g := by
  simpa only [smul_eq_mul] using convexOn_exp.2 (mem_univ f) (mem_univ g) ha.1
    (sub_nonneg.2 ha.2) (show a + (1 - a) = 1 by ring)

theorem exp_convex_mix_lt {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) {f g : ℝ} (hfg : f ≠ g) :
    Real.exp (a * f + (1 - a) * g) < a * Real.exp f + (1 - a) * Real.exp g := by
  simpa only [smul_eq_mul] using strictConvexOn_exp.2 (mem_univ f) (mem_univ g) hfg ha.1
    (sub_pos.2 ha.2) (show a + (1 - a) = 1 by ring)

theorem integrable_exp_convex_mix {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable (fun x => Real.exp (f x)) μ) (hg : Integrable (fun x => Real.exp (g x)) μ)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    Integrable (fun x => Real.exp (a * f x + (1 - a) * g x)) μ := by
  refine ((hf.const_mul a).add (hg.const_mul (1 - a))).mono'
    (Real.measurable_exp.comp ((measurable_const.mul hfm).add (measurable_const.mul hgm))).aestronglyMeasurable
    (.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_convex_mix_le ha (f x) (g x)

/-- Two normalized positive exponential densities have a normalized
convex mixture whose expectation is at most one. -/
theorem integral_exp_convex_mix_le_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable (fun x => Real.exp (f x)) μ) (hg : Integrable (fun x => Real.exp (g x)) μ)
    (hfn : (∫ x, Real.exp (f x) ∂μ) = 1) (hgn : (∫ x, Real.exp (g x) ∂μ) = 1)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    (∫ x, Real.exp (a * f x + (1 - a) * g x) ∂μ) ≤ 1 := by
  have hb := integral_mono (integrable_exp_convex_mix hfm hgm hf hg ha)
    ((hf.const_mul a).add (hg.const_mul (1 - a))) (fun x => exp_convex_mix_le ha (f x) (g x))
  simp only [Pi.add_apply] at hb
  rw [integral_add (hf.const_mul a) (hg.const_mul (1 - a)), integral_const_mul, integral_const_mul,
    hfn, hgn] at hb
  linarith

/-- For strictly interior weights, equality of the normalized
exponential comparison forces the logarithmic tilts to agree almost surely. -/
theorem ae_eq_of_integral_exp_convex_mix_eq_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable (fun x => Real.exp (f x)) μ) (hg : Integrable (fun x => Real.exp (g x)) μ)
    (hfn : (∫ x, Real.exp (f x) ∂μ) = 1) (hgn : (∫ x, Real.exp (g x) ∂μ) = 1)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (he : (∫ x, Real.exp (a * f x + (1 - a) * g x) ∂μ) = 1) : f =ᵐ[μ] g := by
  have ha' : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1.le, ha.2.le⟩
  have hi := integrable_exp_convex_mix hfm hgm hf hg ha'
  have hu := (hf.const_mul a).add (hg.const_mul (1 - a))
  have hmean : (∫ x, a * Real.exp (f x) + (1 - a) * Real.exp (g x) ∂μ) = 1 := by
    rw [integral_add (hf.const_mul a) (hg.const_mul (1 - a)), integral_const_mul, integral_const_mul, hfn, hgn]
    ring
  have heq := (integral_eq_iff_of_ae_le hi hu (.of_forall fun x => exp_convex_mix_le ha' (f x) (g x))).1
    (he.trans hmean.symm)
  filter_upwards [heq] with x hx
  by_contra hne
  exact (exp_convex_mix_lt ha hne).ne hx

end SpinGlass
