import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# FieldTruncation analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators ENNReal NNReal

namespace SpinGlass.Aristotle

noncomputable section

/-! ## Field truncation and uniform continuity

Search tag: `PARISI_LB_TRUNCATION`. Keywords: clipping, bounded approximation,
finite second moment, L1, L2, product law, shared replica field, pressure continuity.

Consumers: bounded-field approximation for Proposition 14.5.8 and the final
finite-second-moment theorem. Truncation is performed coordinatewise under a
coupling. The same truncated coordinate is used for both replicas.
-/

/-- Symmetric field truncation to the interval with endpoints -R and R when R is
nonnegative. `map_pi_clip` applies this same map independently at every site. -/
def clip (R x : ℝ) : ℝ := max (-R) (min R x)

@[fun_prop]
theorem continuous_clip (R : ℝ) : Continuous (clip R) := by
  unfold clip; fun_prop

theorem clip_eq_self {R x : ℝ} (h : |x| ≤ R) : clip R x = x := by
  unfold clip
  rw [min_eq_right (abs_le.1 h).2, max_eq_right (abs_le.1 h).1]

/-- Pointwise domination for bounded support and dominated convergence of clip errors. -/
theorem clip_bounds {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    |clip R x| ≤ R ∧ |clip R x| ≤ |x| ∧
      |x - clip R x| ≤ |x| := by
  have key : clip R x = x ∧ |x| ≤ R ∨ clip R x = R ∧ R ≤ x ∨ clip R x = -R ∧ x ≤ -R := by
    unfold clip
    rcases le_total x (-R) with h | h
    · exact .inr (.inr ⟨by rw [min_eq_right (by linarith), max_eq_left h], h⟩)
    rcases le_total x R with h' | h'
    · exact .inl ⟨by rw [min_eq_right h', max_eq_right h], abs_le.2 ⟨h, h'⟩⟩
    · exact .inr (.inl ⟨by rw [min_eq_left h', max_eq_right (by linarith)], h'⟩)
  rcases key with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h]
  · simp [h']
  · rw [abs_of_nonneg hR, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact ⟨le_rfl, h', by linarith⟩
  · rw [abs_neg, abs_of_nonneg hR, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    exact ⟨le_rfl, by linarith, by linarith⟩

/-- The L1 truncation cost is finite under a finite first absolute moment. -/
theorem integrable_clip_error {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable id μ) {R : ℝ} (hR : 0 ≤ R) :
    Integrable (fun x => |x - clip R x|) μ := by
  exact hint.abs.mono' (by fun_prop) (.of_forall fun x => by
    simpa using (clip_bounds hR x).2.2)

/-- L1 field approximation as the cutoff tends to infinity; supplies the vanishing
error in `eventual_lower_of_uniform_approximation`. -/
theorem tendsto_integral_clip_error {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable id μ) :
    Tendsto (fun R : ℝ => ∫ x, |x - clip R x| ∂μ) atTop (𝓝 0) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun R x => |x - clip R x|) (f := fun _ => 0) (fun x => |x|)
    (.of_forall fun R => by fun_prop)
    (eventually_ge_atTop 0 |>.mono fun R hR => .of_forall fun x => by
      simpa using (clip_bounds hR x).2.2)
    hint.abs
    (.of_forall fun x => tendsto_const_nhds.congr' <|
      (eventually_ge_atTop |x|).mono fun R hR => by simp [clip_eq_self hR])
  simpa using this

/-- L2 field approximation under the capstone's finite-second-moment assumption. -/
theorem tendsto_integral_sq_clip_error {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x ^ 2) μ) :
    Tendsto (fun R : ℝ => ∫ x, (x - clip R x) ^ 2 ∂μ) atTop (𝓝 0) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun R x => (x - clip R x) ^ 2) (f := fun _ => 0) (fun x => x ^ 2)
    (.of_forall fun R => by fun_prop)
    (eventually_ge_atTop 0 |>.mono fun R hR => .of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq.2 (by simpa using (clip_bounds hR x).2.2))
    hint
    (.of_forall fun x => tendsto_const_nhds.congr' <|
      (eventually_ge_atTop |x|).mono fun R hR => by simp [clip_eq_self hR])
  simpa using this

/-- Any positive truncation preserves nondegeneracy. -/
theorem clipped_law_nondegenerate {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x ^ 2) μ)
    (hpos : 0 < ∫ x : ℝ, x ^ 2 ∂μ) {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (Measure.map (clip R) μ) ∧
      Integrable (fun x : ℝ => x ^ 2) (Measure.map (clip R) μ) ∧
      0 < ∫ x : ℝ, x ^ 2 ∂(Measure.map (clip R) μ) := by
  have hm : AEMeasurable (clip R) μ := (continuous_clip R).aemeasurable
  have hsq : Integrable (fun x => clip R x ^ 2) μ := by
    refine Integrable.of_bound (C := R ^ 2) (by fun_prop) (.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (by linarith [(abs_le.1 (clip_bounds hR.le x).1).1])
      (abs_le.1 (clip_bounds hR.le x).1).2
  refine ⟨Measure.isProbabilityMeasure_map hm, ?_, ?_⟩
  · exact (integrable_map_measure (by fun_prop) hm).2 hsq
  rw [integral_map hm (by fun_prop)]
  refine lt_of_le_of_ne (integral_nonneg fun x => sq_nonneg _) fun h => hpos.ne' ?_
  have h0 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hsq).1 h.symm
  refine integral_eq_zero_of_ae (h0.mono fun x hx => ?_)
  simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero] at hx ⊢
  unfold clip at hx
  rcases le_total x R with h1 | h1
  · rw [min_eq_right h1] at hx
    rcases le_total x (-R) with h2 | h2
    · rw [max_eq_left h2] at hx; linarith
    · rwa [max_eq_right h2] at hx
  · rw [min_eq_left h1, max_eq_right (by linarith)] at hx; linarith

/-- Coupled laws are close on every Lipschitz observable; the observable need not be bounded. -/
theorem abs_integral_lipschitz_coupling {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ} {f : ℝ → ℝ}
    {L : ℝ} (hL : 0 ≤ L) (hLip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    |(∫ ω, f (X ω) ∂μ) - (∫ ω, f (Y ω) ∂μ)| ≤
      L * ∫ ω, |X ω - Y ω| ∂μ := by
  have hf : Continuous f := by
    have : LipschitzWith (Real.toNNReal L) f := LipschitzWith.of_dist_le_mul fun x y => by
      simpa [Real.dist_eq, Real.coe_toNNReal _ hL] using hLip x y
    exact this.continuous
  have hint : ∀ Z : Ω → ℝ, Integrable Z μ → Integrable (fun ω => f (Z ω)) μ := fun Z hZ =>
    ((integrable_const (|f 0|)).add (hZ.abs.const_mul L)).mono'
      (hf.comp_aestronglyMeasurable hZ.1) (.of_forall fun ω => by
        have := hLip (Z ω) 0
        rw [sub_zero] at this
        simp only [Real.norm_eq_abs, Pi.add_apply]
        linarith [abs_sub_abs_le_abs_sub (f (Z ω)) (f 0)])
  rw [← integral_sub (hint X hX) (hint Y hY), ← integral_const_mul]
  exact abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
    (.of_forall fun _ => abs_nonneg _) ((hX.sub hY).abs.const_mul L)
    (.of_forall fun ω => hLip _ _))

/-- The normalized product-coordinate truncation cost equals the one-site cost. -/
theorem integral_average_clip_error {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable id μ) {R : ℝ} (hR : 0 ≤ R) {n : ℕ} (hn : 0 < n) :
    (∫ x : Fin n → ℝ, (∑ i, |x i - clip R (x i)|) / n
      ∂(Measure.pi (fun _ : Fin n => μ))) = ∫ x, |x - clip R x| ∂μ := by
  have hi : ∀ i : Fin n, (∫ x : Fin n → ℝ, |x i - clip R (x i)| ∂(Measure.pi fun _ => μ)) =
      ∫ x, |x - clip R x| ∂μ := fun i => by
    conv_rhs => rw [← (measurePreserving_eval (fun _ : Fin n => μ) i).map_eq]
    rw [integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]
  have hint' : ∀ i : Fin n, Integrable (fun x : Fin n → ℝ => |x i - clip R (x i)|)
      (Measure.pi fun _ => μ) := fun i =>
    (measurePreserving_eval (fun _ : Fin n => μ) i).integrable_comp_of_integrable
      (integrable_clip_error hint hR)
  rw [integral_div, integral_finsetSum _ fun i _ => hint' i]
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Coordinatewise truncation has the i.i.d. product of the truncated site laws. -/
theorem map_pi_clip {μ : Measure ℝ} [IsProbabilityMeasure μ] (R : ℝ) (n : ℕ) :
    Measure.map (fun x : Fin n → ℝ => fun i => clip R (x i))
      (Measure.pi (fun _ : Fin n => μ)) =
        Measure.pi (fun _ : Fin n => Measure.map (clip R) μ) := by
  exact Measure.pi_map_pi fun _ => (continuous_clip R).aemeasurable

end

end SpinGlass.Aristotle
