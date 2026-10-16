import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Localization analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators ENNReal NNReal

namespace SpinGlass.Aristotle

noncomputable section

/-! ## Localization with the required uniform quantifiers

Search tag: `PARISI_LB_LOCALIZATION`. Keywords: bad overlap event, finite overlap
count, exponential decay, uniform time threshold, joint branch probability.

Consumer: (14.110). The coefficient in the main estimate is fixed before the
auxiliary accuracy. Finite overlap sums retain their volume-dependent cardinality.
-/

/-- The quadratic main estimate supplies the gap needed by concentration. -/
theorem pressure_gap_of_overlap_distance {Ψ ψ φ u q K ε : ℝ}
    (hK : 0 < K) (hε : 0 < ε) (hgap : 0 ≤ ψ - φ)
    (hmain : Ψ ≤ 2 * ψ - (u - q) ^ 2 / K)
    (hfar : 2 * K * (ψ - φ + ε) ≤ (u - q) ^ 2) :
    Ψ ≤ 2 * φ - 2 * ε := by
  have : 2 * (ψ - φ + ε) ≤ (u - q) ^ 2 / K := by
    rw [le_div_iff₀ hK]; linarith
  linarith

/-- At most 2n+1 possible overlaps: a uniform exponential bound survives summation. -/
theorem finite_overlap_sum_le {ι : Type*} (s : Finset ι) {n : ℕ}
    (hcard : s.card ≤ 2 * n + 1) {p : ι → ℝ} {C c : ℝ} (hC : 0 ≤ C)
    (hp : ∀ i ∈ s, p i ≤ C * Real.exp (-c * n)) :
    ∑ i ∈ s, p i ≤ (2 * (n : ℝ) + 1) * C * Real.exp (-c * n) := by
  calc ∑ i ∈ s, p i ≤ s.card • (C * Real.exp (-c * n)) := Finset.sum_le_card_nsmul _ _ _ hp
    _ ≤ (2 * (n : ℝ) + 1) * C * Real.exp (-c * n) := by
      rw [nsmul_eq_mul, mul_assoc]
      gcongr
      exact_mod_cast hcard

/-- Exponential decay absorbs the linear number of possible overlaps.
Used by `eventually_uniform_finite_overlap_sum` to choose one volume threshold. -/
theorem eventually_overlap_exponential_small {C c ε : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (2 * (n : ℝ) + 1) * C * Real.exp (-c * n) ≤ ε := by
  have hlin : Tendsto (fun n : ℕ => c * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hlin
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hlin
  have : Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) * C * Real.exp (-c * n)) atTop (𝓝 0) := by
    have := ((h1.const_mul (2 / c)).add h0).mul_const C
    simp only [Function.comp_def, pow_one, pow_zero, one_mul, mul_zero, zero_add,
      zero_mul] at this
    refine this.congr fun n => ?_
    rw [neg_mul]
    field_simp
  exact this.eventually (ge_mem_nhds hε)

/-- Uniformity in time and level is preserved when summing constrained masses. -/
theorem eventually_uniform_finite_overlap_sum
    {T I : Type*} {S : ℕ → Finset I} {p : ℕ → T → I → ℝ}
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hcard : ∀ n, (S n).card ≤ 2 * n + 1)
    (hbound : ∀ n t i, i ∈ S n → p n t i ≤ C * Real.exp (-c * n)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t, ∑ i ∈ S n, p n t i ≤ ε := by
  intro ε hε
  filter_upwards [eventually_overlap_exponential_small hC hc hε] with n hn t
  exact (finite_overlap_sum_le _ (hcard n) hC (hbound n t)).trans hn

/-- Joint branch mass is enough; no division by its probability is necessary. -/
theorem localized_joint_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {R : Ω → ℝ} {B : Set Ω}
    (hR : Measurable R) (hB : MeasurableSet B)
    (hRbound : ∀ᵐ ω ∂μ, R ω ∈ Icc (-1 : ℝ) 1)
    {q a ε : ℝ} (hq : q ∈ Icc (-1 : ℝ) 1) (ha : 0 ≤ a)
    (hbad : μ.real (B ∩ {ω | a ≤ (R ω - q) ^ 2}) ≤ ε) :
    (∫ ω in B, (R ω - q) ^ 2 ∂μ) ≤ a * μ.real B + 4 * ε := by
  set S := {ω | a ≤ (R ω - q) ^ 2}
  have hS : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hI : Integrable (fun ω => a + S.indicator (fun _ => (4 : ℝ)) ω) (μ.restrict B) :=
    (integrable_const _).add ((integrable_const _).indicator hS)
  calc (∫ ω in B, (R ω - q) ^ 2 ∂μ)
      ≤ ∫ ω in B, (a + S.indicator (fun _ => (4 : ℝ)) ω) ∂μ := by
        refine integral_mono_of_nonneg (.of_forall fun _ => sq_nonneg _) hI ?_
        refine ae_restrict_of_ae (hRbound.mono fun ω hω => ?_)
        dsimp only
        by_cases h : ω ∈ S
        · rw [indicator_of_mem h]
          obtain ⟨h1, h2⟩ := hω
          obtain ⟨h3, h4⟩ := hq
          nlinarith
        · rw [indicator_of_notMem h]
          simp only [S, mem_ofPred_eq, not_le] at h
          linarith
    _ = a * μ.real B + 4 * μ.real (B ∩ S) := by
        rw [integral_add (integrable_const _) ((integrable_const _).indicator hS),
          integral_indicator_const _ hS, setIntegral_const]
        simp only [smul_eq_mul, measureReal_restrict_apply hS]
        rw [inter_comm]; ring
    _ ≤ a * μ.real B + 4 * ε := by linarith

/-- Sum joint localization bounds with an explicit total error budget. One may
allocate ε divided by the number of levels to each error; proportionality to a
branch probability is not assumed. -/
theorem weighted_localization_sum {ι : Type*} [Fintype ι]
    {w x e : ι → ℝ} {a ε : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i ≤ 1) (ha : 0 ≤ a) (herr : ∑ i, e i ≤ ε)
    (hx : ∀ i, x i ≤ a * w i + e i) :
    ∑ i, x i ≤ a + ε := by
  calc ∑ i, x i ≤ ∑ i, (a * w i + e i) := Finset.sum_le_sum fun i _ => hx i
    _ = a * ∑ i, w i + ∑ i, e i := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ a + ε := by nlinarith

end

end SpinGlass.Aristotle
