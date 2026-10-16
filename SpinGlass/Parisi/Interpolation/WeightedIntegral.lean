import SpinGlass.Parisi.Interpolation.WeightedDerivative

/-!
# Integrated weighted interpolation and uniform trace bounds

The exact derivative integrates on every closed subinterval of the
interpolation. A covariance supremum bound controls the trace independently
of the number of states and of the nonzero weights.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace SpinGlass.FiniteGibbs

noncomputable section

variable {α Ω : Type*} [Fintype α] [MeasurableSpace Ω] {P : Measure Ω}
    {K₁ K₂ : α → α → ℝ}

/-- Normalizing the Gibbs weights removes the state count from the trace
bound. This remains valid when some weights vanish. -/
theorem abs_wGuerraTrace_le_of_cov_bound
    (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (K₁ K₂ : α → α → ℝ) (n : ℕ) (H : EnergySpace α) {D : ℝ}
    (hD : ∀ x y, |K₁ x y - K₂ x y| ≤ D) :
    |wGuerraTrace wt K₁ K₂ n H| ≤ D / n := by
  have hg := wGibbs_nonneg wt hwt hne H
  have hs := sum_wGibbs wt hwt hne H
  have hd : |∑ x, (K₁ x x - K₂ x x) * wGibbs wt H x| ≤ D := by
    calc
      _ ≤ ∑ x, |(K₁ x x - K₂ x x) * wGibbs wt H x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, D * wGibbs wt H x := by
        apply Finset.sum_le_sum
        intro x _
        rw [abs_mul, abs_of_nonneg (hg x)]
        exact mul_le_mul_of_nonneg_right (hD x x) (hg x)
      _ = D := by rw [← Finset.mul_sum, hs, mul_one]
  have ho : |∑ x, ∑ y, (K₁ x y - K₂ x y) *
      (wGibbs wt H x * wGibbs wt H y)| ≤ D := by
    calc
      _ ≤ ∑ x, ∑ y, |(K₁ x y - K₂ x y) *
          (wGibbs wt H x * wGibbs wt H y)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ x, ∑ y, D * (wGibbs wt H x * wGibbs wt H y) := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro y _
        rw [abs_mul, abs_of_nonneg (mul_nonneg (hg x) (hg y))]
        exact mul_le_mul_of_nonneg_right (hD x y) (mul_nonneg (hg x) (hg y))
      _ = D := by
        simp_rw [← mul_assoc, ← Finset.mul_sum, hs, mul_one]
        rw [← Finset.mul_sum, hs, mul_one]
  unfold wGuerraTrace
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * (n : ℝ)))]
  calc
    _ ≤ (1 / (2 * (n : ℝ))) * (D + D) :=
      mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hd ho)) (by positivity)
    _ = D / n := by ring

variable (G₁ : GaussianField (α := α) P K₁) (G₂ : GaussianField (α := α) P K₂)

theorem continuous_integral_wGuerraTrace (hindep : G₁.U ⟂ᵢ[P] G₂.U)
    (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (c : EnergySpace α) (n : ℕ) :
    Continuous (fun t => ∫ p : PairSpace α,
      wGuerraTrace wt K₁ K₂ n (gaussianInterp t p + c) ∂pairLaw G₁ G₂) := by
  have := isGaussian_pairLaw G₁ G₂ hindep
  refine continuous_of_dominated (fun t => ?_)
    (bound := fun _ => (1 / (2 * (n : ℝ))) *
      ((∑ x, |K₁ x x - K₂ x x|) + ∑ x, ∑ y, |K₁ x y - K₂ x y|))
    (fun t => Filter.Eventually.of_forall fun p => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun p => ?_)
  · exact ((continuous_wGuerraTrace wt hwt hne K₁ K₂ n).comp
      ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_wGuerraTrace_le wt hwt hne _ _ n _
  · exact (continuous_wGuerraTrace wt hwt hne K₁ K₂ n).comp
      ((continuous_gaussianInterp_apply p).add continuous_const)

/-- Exact finite weighted interpolation on a closed subinterval, including
the initial and terminal endpoints. -/
theorem wGuerraPhi_sub_eq_integral (hindep : G₁.U ⟂ᵢ[P] G₂.U)
    (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (c : EnergySpace α) (n : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    wGuerraPhi G₁ G₂ wt c n b - wGuerraPhi G₁ G₂ wt c n a =
      ∫ t in a..b, ∫ p : PairSpace α,
        wGuerraTrace wt K₁ K₂ n (gaussianInterp t p + c) ∂pairLaw G₁ G₂ := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · exact (continuousOn_wGuerraPhi G₁ G₂ hindep wt hwt hne c n).mono
      (fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩)
  · intro t ht
    exact hasDerivAt_wGuerraPhi G₁ G₂ hindep wt hwt hne c n
      ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩
  · exact (continuous_integral_wGuerraTrace G₁ G₂ hindep wt hwt hne c n).intervalIntegrable a b

end

end SpinGlass.FiniteGibbs
