import Mathlib.Analysis.Calculus.MeanValue

/-!
# Infimum analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped BigOperators

namespace SpinGlass.Aristotle

noncomputable section

/-! ## Closed competitors and global near-minimality

Search tag: `PARISI_LB_INFIMUM`. Keywords: global infimum, closed domain,
MIN epsilon, split competitor, density, perturbation of the variational value.

Consumer: `Minimizer/Full.lean` and `Variational/ParisiMVariation.lean`.
The set S below is the set of ordinary admissible functional values. Reduction
of a closed minimum supplies its membership in S; no comparison across different
level counts is inferred from fixed-level minimality.
-/

/-- Transfer a lower bound through a value-preserving reduction of an attained minimum. -/
theorem sInf_le_of_reduced_minimum {X : Type*} {D : Set X} {F : X → ℝ}
    {S : Set ℝ} (hS : BddBelow S) {x y : X}
    (hy : IsMinOn F D y) (hvalue : F y ∈ S) (hx : x ∈ D) :
    sInf S ≤ F x := by
  exact (csInf_le hS hvalue).trans (hy hx)

/-- Alternative route when ordinary competitors are dense among closed competitors. -/
theorem lower_bound_on_closure {X : Type*} [TopologicalSpace X]
    {D : Set X} {F : X → ℝ} {b : ℝ}
    (hF : ContinuousOn F (closure D)) (hD : ∀ x ∈ D, b ≤ F x) :
    ∀ x ∈ closure D, b ≤ F x := by
  intro x hx
  exact ContinuousWithinAt.closure_le hx continuousWithinAt_const
    ((hF x hx).mono subset_closure) hD

/-- Global near-minimality applies to a split even though the level count changes. -/
theorem near_minimum_competitor {P I ε Φ : ℝ}
    (hnear : P < I + ε) (hcompetitor : I ≤ Φ) : P - ε < Φ := by
  linarith

/-- Uniform perturbations of a nonempty family perturb its infimum by the same amount. -/
theorem abs_sInf_range_sub_le {ι : Type*} [Nonempty ι]
    {F G : ι → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hF : BddBelow (range F)) (hG : BddBelow (range G))
    (h : ∀ i, |F i - G i| ≤ δ) :
    |sInf (range F) - sInf (range G)| ≤ δ := by
  have h₁ : iInf F - δ ≤ iInf G :=
    le_ciInf fun i => by linarith [ciInf_le hF i, (abs_le.1 (h i)).2]
  have h₂ : iInf G - δ ≤ iInf F :=
    le_ciInf fun i => by linarith [ciInf_le hG i, (abs_le.1 (h i)).1]
  rw [← iInf, ← iInf, abs_sub_le_iff]
  constructor <;> linarith

end

end SpinGlass.Aristotle
