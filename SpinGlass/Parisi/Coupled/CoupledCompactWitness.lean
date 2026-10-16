import Mathlib.Topology.Order.Compact
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Choose

/-!
# Compact uniformization of scalar comparison witnesses

The witness bounds are continuous independently of the constrained
finite-volume pressure. A finite cover gives a positive uniform gap,
without requiring continuity of that pressure in its overlap constraint.
-/

open Set

namespace SpinGlass

/-- A finite family of positive numbers has a common positive lower bound,
including when the indexing type is empty. -/
theorem exists_uniform_positive_lower_bound_of_finite {ι : Type*} [Finite ι]
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ d i := by
  classical
  let := Fintype.ofFinite ι
  by_cases hne : (Finset.univ : Finset ι).Nonempty
  · exact ⟨Finset.univ.inf' hne d,
      (Finset.lt_inf'_iff hne).2 (fun i _ => hd i),
      fun i => Finset.inf'_le d (Finset.mem_univ i)⟩
  · exact ⟨1, zero_lt_one, fun i => (hne ⟨i, Finset.mem_univ i⟩).elim⟩

/-- Pointwise positive continuous scalar witnesses give a uniform
positive gap on a compact set, also when that set is empty. -/
theorem exists_uniform_positive_continuous_witness {E W : Type*} [TopologicalSpace E]
    {s : Set E} (hs : IsCompact s) (g : W → E → ℝ)
    (hc : ∀ w, ContinuousOn (g w) s) (hp : ∀ x ∈ s, ∃ w, 0 < g w x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s, ∃ w, δ ≤ g w x := by
  classical
  let : CompactSpace s := isCompact_iff_compactSpace.1 hs
  choose w hw using (fun x : s => hp x.1 x.2)
  let e : s → ℝ := fun x => g (w x) x / 2
  let U : s → Set s := fun x => {y | e x < g (w x) y}
  have hU (x : s) : IsOpen (U x) := isOpen_lt continuous_const (hc (w x)).domRestrict
  have hcover : (univ : Set s) ⊆ ⋃ x, U x := by
    intro y _
    apply mem_iUnion.2
    refine ⟨y, ?_⟩
    change g (w y) y / 2 < g (w y) y
    linarith [hw y]
  obtain ⟨f, hf⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  obtain ⟨δ, hδ, hbound⟩ := exists_uniform_positive_lower_bound_of_finite
    (fun x : f => e x) (fun x => half_pos (hw x))
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hf (mem_univ (⟨x, hx⟩ : s)))
  exact ⟨w y, (hbound ⟨y, hy⟩).trans (le_of_lt hxy)⟩

end SpinGlass
