import SpinGlass.Parisi.Variational.ParisiExponentialMix

/-!
# Normalized exponential entropy comparison

The tangent inequality for the exponential gives the zero-mass
dual comparison. Equality forces the two actual normalized densities
to agree. Integrability is explicit for later Gaussian specialization.
-/

open MeasureTheory ProbabilityTheory Set

namespace SpinGlass

theorem exp_mul_sub_le_exp_sub (f g : ℝ) :
    Real.exp g * (f - g) ≤ Real.exp f - Real.exp g := by
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (f - g)) (Real.exp_pos g).le
  have he : Real.exp g * Real.exp (f - g) = Real.exp f := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hh
  nlinarith

theorem exp_mul_sub_lt_exp_sub {f g : ℝ} (hfg : f ≠ g) :
    Real.exp g * (f - g) < Real.exp f - Real.exp g := by
  have hh := mul_lt_mul_of_pos_left (Real.add_one_lt_exp (sub_ne_zero.2 hfg)) (Real.exp_pos g)
  have he : Real.exp g * Real.exp (f - g) = Real.exp f := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hh
  nlinarith

/-- The relative logarithm has nonpositive mean under the second
normalized exponential density. -/
theorem integral_exp_mul_sub_le_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ}
    (hf : Integrable (fun x => Real.exp (f x)) μ) (hg : Integrable (fun x => Real.exp (g x)) μ)
    (hfg : Integrable (fun x => Real.exp (g x) * (f x - g x)) μ)
    (hfn : (∫ x, Real.exp (f x) ∂μ) = 1) (hgn : (∫ x, Real.exp (g x) ∂μ) = 1) :
    (∫ x, Real.exp (g x) * (f x - g x) ∂μ) ≤ 0 := by
  have hb := integral_mono hfg (hf.sub hg) (fun x => exp_mul_sub_le_exp_sub (f x) (g x))
  simp only [Pi.sub_apply] at hb
  rw [integral_sub hf hg, hfn, hgn, sub_self] at hb
  exact hb

/-- Equality in the normalized entropy comparison forces the
logarithmic densities to agree almost surely. -/
theorem ae_eq_of_integral_exp_mul_sub_eq_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ}
    (hf : Integrable (fun x => Real.exp (f x)) μ) (hg : Integrable (fun x => Real.exp (g x)) μ)
    (hfg : Integrable (fun x => Real.exp (g x) * (f x - g x)) μ)
    (hfn : (∫ x, Real.exp (f x) ∂μ) = 1) (hgn : (∫ x, Real.exp (g x) ∂μ) = 1)
    (he : (∫ x, Real.exp (g x) * (f x - g x) ∂μ) = 0) : f =ᵐ[μ] g := by
  have hmean : (∫ x, Real.exp (f x) - Real.exp (g x) ∂μ) = 0 := by
    rw [integral_sub hf hg, hfn, hgn, sub_self]
  have heq := (integral_eq_iff_of_ae_le hfg (hf.sub hg)
    (.of_forall fun x => exp_mul_sub_le_exp_sub (f x) (g x))).1 (he.trans hmean.symm)
  filter_upwards [heq] with x hx
  by_contra hne
  exact (exp_mul_sub_lt_exp_sub hne).ne hx

end SpinGlass
