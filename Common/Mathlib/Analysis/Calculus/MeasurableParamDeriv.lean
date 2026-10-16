/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Measurability of a derivative in a parameter

`measurable_deriv_param`: if `v ↦ Φ v x` is differentiable at `v₀` for every parameter `x` with
derivative `D x`, and each `Φ v` is measurable in `x`, then `D` is measurable. The derivative is
a pointwise limit of measurable difference quotients within the domain, so no joint
measurability, continuity or domination is needed. (Mathlib's `measurable_deriv` is the
measurability of `deriv f` in the *differentiation* variable, a different statement.)
-/

open MeasureTheory Filter Topology

/-- A derivative within a fixed domain is measurable in the evaluation
parameter whenever the domain has points approaching the differentiation point.
The difference quotients stay in that domain. -/
theorem measurable_derivWithin_param {X : Type*} [MeasurableSpace X]
    {Φ : ℝ → X → ℝ} {D : X → ℝ} {s : Set ℝ} {v₀ : ℝ}
    (hs : AccPt v₀ (𝓟 s)) (hm : ∀ v, Measurable (Φ v))
    (hd : ∀ x, HasDerivWithinAt (fun v => Φ v x) (D x) s v₀) :
    Measurable D := by
  have : (𝓝[s \ {v₀}] v₀).NeBot := accPt_principal_iff_nhdsWithin.1 hs
  obtain ⟨u, hu⟩ := Filter.exists_seq_tendsto (𝓝[s \ {v₀}] v₀)
  have hseq : ∀ x, Tendsto
      (fun n => (Φ (u n) x - Φ v₀ x) / (u n - v₀)) atTop (𝓝 (D x)) := by
    intro x
    simpa only [Function.comp_def, slope_def_field] using
      (hasDerivWithinAt_iff_tendsto_slope.1 (hd x)).comp hu
  exact measurable_of_tendsto_metrizable
    (fun n => ((hm (u n)).sub (hm v₀)).div_const _) (tendsto_pi_nhds.2 hseq)

/-- A full-domain derivative is measurable in the evaluation parameter whenever
all slices are measurable. This is the within-domain result on the full real line. -/
theorem measurable_deriv_param {X : Type*} [MeasurableSpace X] {Φ : ℝ → X → ℝ} {D : X → ℝ}
    {v₀ : ℝ} (hm : ∀ v, Measurable (Φ v)) (hd : ∀ x, HasDerivAt (fun v => Φ v x) (D x) v₀) :
    Measurable D :=
  measurable_derivWithin_param
    (uniqueDiffWithinAt_univ (𝕜 := ℝ) (x := v₀)).accPt hm
    (fun x => (hd x).hasDerivWithinAt)

/-- Admissible endpoint derivatives on a nontrivial closed interval are
measurable in the evaluation parameter. -/
theorem measurable_derivWithin_param_Icc {X : Type*} [MeasurableSpace X]
    {Φ : ℝ → X → ℝ} {D : X → ℝ} {a b v₀ : ℝ}
    (hab : a < b) (hv : v₀ ∈ Set.Icc a b) (hm : ∀ v, Measurable (Φ v))
    (hd : ∀ x, HasDerivWithinAt (fun v => Φ v x) (D x) (Set.Icc a b) v₀) :
    Measurable D :=
  measurable_derivWithin_param ((uniqueDiffOn_Icc hab) _ hv).accPt hm hd

/-- The interval version needs measurability only for admissible parameter
values; extending the functions by zero outside the interval gives the same
within derivative. -/
theorem measurable_derivWithin_param_Icc_of_measurableOn {X : Type*} [MeasurableSpace X]
    {Φ : ℝ → X → ℝ} {D : X → ℝ} {a b v₀ : ℝ}
    (hab : a < b) (hv : v₀ ∈ Set.Icc a b)
    (hm : ∀ v ∈ Set.Icc a b, Measurable (Φ v))
    (hd : ∀ x, HasDerivWithinAt (fun v => Φ v x) (D x) (Set.Icc a b) v₀) :
    Measurable D := by
  classical
  apply measurable_derivWithin_param_Icc hab hv
    (Φ := fun v => if v ∈ Set.Icc a b then Φ v else fun _ => 0)
  · intro v
    split_ifs with hv'
    · exact hm v hv'
    · exact measurable_const
  · intro x
    exact (hd x).congr_of_mem (fun v hv' => by simp only [ite_eq_left hv']) hv
