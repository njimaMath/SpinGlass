import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi

/-!
# BoundedDifferences analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators ENNReal NNReal

namespace SpinGlass.Aristotle

noncomputable section

/-! ## Bounded-field fluctuations and pressure gaps

Search tag: `PARISI_LB_CONCENTRATION`. Keywords: McDiarmid, Hoeffding, MGF,
conditional Gaussian concentration, field fluctuations, capped exponential.

Consumer: the random-field transfer after (14.123). Gaussian fluctuation
around a conditional mean is already supported in the repository. The first
lemma supplies concentration of that mean for bounded independent coordinates.
The next lemma combines the two fluctuations without asserting a conditional
gap from a law-averaged gap. No independence of the two fluctuations is assumed.
-/

/-- Bounded coordinate oscillations bound the total oscillation. -/
theorem abs_sub_le_sum_of_bounded_differences {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : (ι → ℝ) → ℝ} {c : ι → ℝ}
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ c i) (x y : ι → ℝ) :
    |F y - F x| ≤ ∑ i, c i := by
  have key : ∀ s : Finset ι, |F (s.piecewise y x) - F x| ≤ ∑ i ∈ s, c i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.piecewise_insert, Finset.sum_insert ha]
      calc |F (Function.update (s.piecewise y x) a (y a)) - F x|
          ≤ |F (Function.update (s.piecewise y x) a (y a)) - F (s.piecewise y x)| +
            |F (s.piecewise y x) - F x| := abs_sub_le _ _ _
        _ ≤ c a + ∑ i ∈ s, c i := add_le_add (hosc _ _ _) ih
  simpa using key Finset.univ

theorem abs_le_of_bounded_differences {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : (ι → ℝ) → ℝ} {c : ι → ℝ}
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ c i) (x : ι → ℝ) :
    |F x| ≤ |F 0| + ∑ i, c i := by
  have := abs_sub_le_sum_of_bounded_differences hosc 0 x
  have := abs_sub_abs_le_abs_sub (F x) (F 0)
  linarith

theorem integrable_of_bounded_differences {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {κ : Measure Ω} [IsFiniteMeasure κ] {F : (ι → ℝ) → ℝ} {c : ι → ℝ}
    (hF : Measurable F) (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ c i)
    {φ : Ω → ι → ℝ} (hφ : Measurable φ) :
    Integrable (fun ω => F (φ ω)) κ :=
  Integrable.of_bound (C := |F 0| + ∑ i, c i) (hF.comp hφ).aestronglyMeasurable
    (.of_forall fun ω => abs_le_of_bounded_differences hosc (φ ω))

theorem integrable_exp_of_bounded_differences {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {κ : Measure Ω} [IsFiniteMeasure κ] {F : (ι → ℝ) → ℝ} {c : ι → ℝ}
    (hF : Measurable F) (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ c i)
    {φ : Ω → ι → ℝ} (hφ : Measurable φ) (t E : ℝ) :
    Integrable (fun ω => Real.exp (t * (F (φ ω) - E))) κ := by
  refine Integrable.of_bound (C := Real.exp (|t| * (|F 0| + ∑ i, c i + |E|)))
    (Real.continuous_exp.measurable.comp
      (((hF.comp hφ).sub_const E).const_mul t)).aestronglyMeasurable
    (.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul]
  gcongr
  have := abs_le_of_bounded_differences hosc (φ ω)
  have := abs_sub (F (φ ω)) E
  linarith

/-- McDiarmid's exponential-moment bound, by induction on the number of coordinates. -/
theorem integral_exp_le_of_bounded_differences : ∀ {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {F : (Fin n → ℝ) → ℝ} (hF : Measurable F)
    (c : Fin n → ℝ) (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ c i) (t : ℝ),
    (∫ x, Real.exp (t * (F x - ∫ y, F y ∂(Measure.pi μ))) ∂(Measure.pi μ)) ≤
      Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8)
  | 0, μ, _, F, _, c, _, t => by
    have hconst : ∀ x, F x = F default := fun x => congrArg F (Subsingleton.elim x default)
    simp [hconst]
  | n + 1, μ, _, F, hF, c, hosc, t => by
    classical
    set ν := Measure.pi fun j : Fin n => μ j.succ
    set φ : ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun p => Fin.cons p.1 p.2
    have hφ : MeasurePreserving φ ((μ 0).prod ν) (Measure.pi μ) := by
      have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
      convert! hmp using 1
      ext p : 1
      simp [φ, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero']
    have hφm : Measurable φ := hφ.measurable
    have htrans : ∀ f : (Fin (n + 1) → ℝ) → ℝ, Measurable f →
        ∫ x, f x ∂(Measure.pi μ) = ∫ p, f (φ p) ∂((μ 0).prod ν) := fun f hf => by
      rw [← hφ.map_eq, integral_map hφm.aemeasurable hf.aestronglyMeasurable]
    set G : ℝ → (Fin n → ℝ) → ℝ := fun x₀ x' => F (Fin.cons x₀ x')
    have hGm : ∀ x₀, Measurable (G x₀) := fun x₀ =>
      hF.comp (hφm.comp (measurable_prodMk_left (m := inferInstance)))
    have hGosc : ∀ x₀ x' j y, |G x₀ (Function.update x' j y) - G x₀ x'| ≤ c j.succ := by
      intro x₀ x' j y
      simp only [G]
      rw [Fin.cons_update]
      exact hosc _ _ _
    have hGint : ∀ x₀, Integrable (G x₀) ν := fun x₀ =>
      integrable_of_bounded_differences (hGm x₀) (hGosc x₀) measurable_id
    set g : ℝ → ℝ := fun x₀ => ∫ x', G x₀ x' ∂ν
    have hgm : Measurable g :=
      ((hF.comp hφm).stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    have hgosc : ∀ x₀ y₀, g y₀ ≤ g x₀ + c 0 := by
      intro x₀ y₀
      have hpt : ∀ x', G y₀ x' ≤ G x₀ x' + c 0 := fun x' => by
        have := hosc (Fin.cons x₀ x') 0 y₀
        rw [Fin.update_cons_zero] at this
        linarith [le_abs_self (G y₀ x' - G x₀ x')]
      calc g y₀ ≤ ∫ x', (G x₀ x' + c 0) ∂ν :=
            integral_mono (hGint y₀) ((hGint x₀).add (integrable_const _)) hpt
        _ = g x₀ + c 0 := by rw [integral_add (hGint x₀) (integrable_const _)]; simp [g]
    have hbdd : BddBelow (range g) :=
      ⟨g 0 - c 0, by rintro _ ⟨y, rfl⟩; linarith [hgosc y 0]⟩
    set a := ⨅ x₀, g x₀
    have hga : ∀ x₀, g x₀ ∈ Icc a (a + c 0) := fun x₀ =>
      ⟨ciInf_le hbdd x₀, by
        have : g x₀ - c 0 ≤ a := le_ciInf fun y => by linarith [hgosc y x₀]
        linarith⟩
    have hE : ∫ y, F y ∂(Measure.pi μ) = ∫ x₀, g x₀ ∂(μ 0) := by
      rw [htrans F hF, integral_prod _ (integrable_of_bounded_differences hF hosc hφm)]
    set E := ∫ y, F y ∂(Measure.pi μ)
    set B' := Real.exp (t ^ 2 * (∑ j : Fin n, c j.succ ^ 2) / 8)
    have hIH : ∀ x₀, ∫ x', Real.exp (t * (G x₀ x' - g x₀)) ∂ν ≤ B' := fun x₀ =>
      integral_exp_le_of_bounded_differences (fun j => μ j.succ) (hGm x₀) (fun j => c j.succ)
        (hGosc x₀) t
    have hH := (hasSubgaussianMGF_of_mem_Icc (μ := μ 0) hgm.aemeasurable
      (ae_of_all _ hga)).mgf_le t
    rw [mgf, ← hE] at hH
    have hnorm : (((‖a + c 0 - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2 = t ^ 2 * c 0 ^ 2 / 8 := by
      rw [add_sub_cancel_left]
      push_cast
      rw [Real.norm_eq_abs, div_pow, sq_abs]
      ring
    rw [hnorm] at hH
    have hexpE : Measurable fun x : Fin (n + 1) → ℝ => Real.exp (t * (F x - E)) :=
      Real.continuous_exp.measurable.comp ((hF.sub_const E).const_mul t)
    have hjoint := integrable_exp_of_bounded_differences (κ := (μ 0).prod ν) hF hosc hφm t E
    rw [htrans _ hexpE, integral_prod _ hjoint]
    have hpt : ∀ x₀, ∫ x', Real.exp (t * (F (φ (x₀, x')) - E)) ∂ν ≤
        Real.exp (t * (g x₀ - E)) * B' := fun x₀ => by
      have : (fun x' => Real.exp (t * (F (φ (x₀, x')) - E))) =
          fun x' => Real.exp (t * (g x₀ - E)) * Real.exp (t * (G x₀ x' - g x₀)) := by
        ext x'; rw [← Real.exp_add]; congr 1; simp only [G, φ]; ring
      rw [this, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hIH x₀) (Real.exp_nonneg _)
    have hgint : Integrable (fun x₀ => Real.exp (t * (g x₀ - E))) (μ 0) := by
      refine Integrable.of_bound (C := Real.exp (|t| * (|a| + |c 0| + |E|)))
        (Real.continuous_exp.measurable.comp ((hgm.sub_const E).const_mul t)).aestronglyMeasurable
        (.of_forall fun x₀ => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul]
      gcongr
      obtain ⟨h1, h2⟩ := hga x₀
      rw [abs_le]
      constructor <;> cases abs_cases a <;> cases abs_cases (c 0) <;> cases abs_cases E <;>
        linarith
    calc ∫ x₀, ∫ x', Real.exp (t * (F (φ (x₀, x')) - E)) ∂ν ∂(μ 0)
        ≤ ∫ x₀, Real.exp (t * (g x₀ - E)) * B' ∂(μ 0) :=
          integral_mono hjoint.integral_prod_left (hgint.mul_const _) hpt
      _ = (∫ x₀, Real.exp (t * (g x₀ - E)) ∂(μ 0)) * B' := integral_mul_const _ _
      _ ≤ Real.exp (t ^ 2 * c 0 ^ 2 / 8) * B' :=
          mul_le_mul_of_nonneg_right hH (Real.exp_nonneg _)
      _ = Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
          rw [← Real.exp_add, Fin.sum_univ_succ]; ring_nf

/-- Product-measure bounded differences in exponential-moment form.
The coordinate oscillation can be obtained on clipped inputs, so the inequality
can be imposed globally even when the original site law has unbounded support. -/
theorem bounded_differences_mgf {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {F : (Fin n → ℝ) → ℝ}
    (hF : Measurable F) (hint : Integrable F (Measure.pi μ))
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ c i) (t : ℝ) :
    Integrable (fun x => Real.exp (t * (F x - ∫ y, F y ∂(Measure.pi μ))))
      (Measure.pi μ) ∧
    (∫ x, Real.exp (t * (F x - ∫ y, F y ∂(Measure.pi μ))) ∂(Measure.pi μ)) ≤
      Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
  exact ⟨integrable_exp_of_bounded_differences hF hosc measurable_id t _,
    integral_exp_le_of_bounded_differences μ hF c hosc t⟩

end

end SpinGlass.Aristotle
