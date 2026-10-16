import Mathlib.Analysis.Calculus.MeanValue

/-!
# Compactness analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped BigOperators

namespace SpinGlass.Aristotle

noncomputable section

/-! ## Uniform gains from local witnesses

Search tag: `PARISI_LB_COMPACTNESS`. Keywords: compact cover, far region,
strict improvement, uniform positive gap, finite witnesses, seven cases.

Consumer: Section 14.8, including the empty far-region case. The witness may
depend on the point, whereas the resulting positive gap is uniform.
-/

/-- A finite set of witnesses suffices, including when the compact set is empty. -/
theorem finite_witnesses_uniform_gap {X I : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {B : I → X → ℝ}
    (hcont : ∀ i, ContinuousOn (B i) K)
    (hneg : ∀ x ∈ K, ∃ i, B i x < 0) :
    ∃ (J : Finset I) (δ : ℝ), 0 < δ ∧
      ∀ x ∈ K, ∃ i ∈ J, B i x ≤ -δ := by
  classical
  choose w hw using fun x : K => hneg x x.2
  choose U hUo hUeq using fun x : K =>
    continuousOn_iff'.1 (hcont (w x)) _ (isOpen_Iio (a := B (w x) x / 2))
  have hxU : ∀ x : K, (x : X) ∈ U x := fun x =>
    ((Set.ext_iff.1 (hUeq x) x).1 ⟨by simp only [mem_preimage, mem_Iio]; linarith [hw x],
      x.2⟩).1
  obtain ⟨t, hcover⟩ := hK.elim_finite_subcover U hUo fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxU _⟩
  obtain ⟨δ, hδ, hδt⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ t, δ ≤ -(B (w x) x / 2) := by
    rcases t.eq_empty_or_nonempty with ht | ht
    · exact ⟨1, one_pos, by simp [ht]⟩
    refine ⟨t.inf' ht fun x => -(B (w x) x / 2), ?_, fun x hx => Finset.inf'_le _ hx⟩
    rw [Finset.lt_inf'_iff]
    intro x _
    linarith [hw x]
  refine ⟨t.image w, δ, hδ, fun y hy => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (hcover hy)
  have := ((Set.ext_iff.1 (hUeq x) y).2 ⟨hyx, hy⟩).1
  simp only [mem_preimage, mem_Iio] at this
  exact ⟨w x, Finset.mem_image_of_mem _ hxt, by linarith [hδt x hxt]⟩

/-- Upgrade pointwise strict improvement to a common positive gap on a compact set.
Use `finite_witnesses_uniform_gap` when the witness set must also be finite. -/
theorem uniform_gap_of_compact_witnesses {X I : Type*} [TopologicalSpace X]
    [Nonempty I] {K : Set X} (hK : IsCompact K) {B : I → X → ℝ}
    (hcont : ∀ i, ContinuousOn (B i) K)
    (hneg : ∀ x ∈ K, ∃ i, B i x < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∃ i, B i x ≤ -δ := by
  obtain ⟨J, δ, hδ, h⟩ := finite_witnesses_uniform_gap hK hcont hneg
  exact ⟨δ, hδ, fun x hx => (h x hx).imp fun i hi => hi.2⟩

/-- Convert a far-region gap into the same quadratic form as a local estimate. -/
theorem uniform_gap_to_quadratic {A B u q δ : ℝ}
    (hδ : 0 < δ) (hu : u ∈ Icc (-1 : ℝ) 1) (hq : q ∈ Icc (-1 : ℝ) 1)
    (hgap : B ≤ A - δ) : B ≤ A - δ / 4 * (u - q) ^ 2 := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hq1, hq2⟩ := hq
  have : (u - q) ^ 2 ≤ 4 := by nlinarith
  nlinarith

/-- Take one positive coefficient for finitely many levels or cases. -/
theorem finite_uniform_positive_coefficient {ι : Type*} [Fintype ι]
    {P : ι → ℝ → Prop}
    (hmono : ∀ i, ∀ c d : ℝ, 0 < d → d ≤ c → P i c → P i d)
    (hex : ∀ i, ∃ c : ℝ, 0 < c ∧ P i c) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, P i c := by
  choose c hc using hex
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := c)
  refine ⟨c j, (hc j).1, fun i => hmono i _ _ (hc j).1 ?_ (hc i).2⟩
  rw [hj]
  exact ciInf_le (Set.finite_range c).bddBelow i

end

end SpinGlass.Aristotle
