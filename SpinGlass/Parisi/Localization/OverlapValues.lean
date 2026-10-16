import SpinGlass.Parisi.Concentration.ParisiBranchConcentration

/-!
# The finite set of physical Ising overlaps

Counting agreeing coordinates places every overlap on a grid of at most
`N + 1` values. The exact image is used in localization, so each member
has a nonempty spin constraint.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace SpinGlass

open FiniteGibbs

/-- All overlap values attained by a physical pair of spin configurations. -/
noncomputable def parisiOverlapValues (N : ℕ) : Finset ℝ :=
  Finset.univ.image (fun σ : Fin 2 → Config N => overlap N (σ 0) (σ 1))

theorem mem_parisiOverlapValues_iff {N : ℕ} {u : ℝ} :
    u ∈ parisiOverlapValues N ↔
      ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u := by
  classical
  simp [parisiOverlapValues]

theorem overlap_mem_parisiOverlapValues {N : ℕ} (σ : Fin 2 → Config N) :
    overlap N (σ 0) (σ 1) ∈ parisiOverlapValues N :=
  mem_parisiOverlapValues_iff.2 ⟨σ, rfl⟩

theorem parisiOverlapValues_mem_Icc {N : ℕ} {u : ℝ}
    (hu : u ∈ parisiOverlapValues N) : u ∈ Icc (-1 : ℝ) 1 := by
  obtain ⟨σ, rfl⟩ := mem_parisiOverlapValues_iff.1 hu
  exact abs_le.1 (abs_overlap_le_one N (σ 0) (σ 1))

/-- The overlap is determined by the number of agreeing coordinates. -/
theorem overlap_eq_agreement_card {N : ℕ} (σ τ : Config N) :
    overlap N σ τ =
      (2 * ((Finset.univ.filter fun i : Fin N => σ i = τ i).card : ℝ) - N) / N := by
  classical
  have he (i : Fin N) : isingSpin (σ i) * isingSpin (τ i) =
      2 * (if σ i = τ i then (1 : ℝ) else 0) - 1 := by
    cases σ i <;> cases τ i <;> norm_num [isingSpin]
  unfold overlap overlapOf spinOf
  simp_rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_boole, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  ring

theorem card_parisiOverlapValues_le (N : ℕ) : (parisiOverlapValues N).card ≤ N + 1 := by
  classical
  let grid := (Finset.range (N + 1)).image (fun j : ℕ => (2 * (j : ℝ) - N) / N)
  have hsub : parisiOverlapValues N ⊆ grid := by
    intro u hu
    obtain ⟨σ, rfl⟩ := mem_parisiOverlapValues_iff.1 hu
    apply Finset.mem_image.2
    refine ⟨(Finset.univ.filter fun i : Fin N => σ 0 i = σ 1 i).card, ?_, ?_⟩
    · apply Finset.mem_range.2
      have hh := Finset.card_filter_le (s := (Finset.univ : Finset (Fin N)))
        (p := fun i => σ 0 i = σ 1 i)
      simpa using Nat.lt_succ_of_le hh
    · exact (overlap_eq_agreement_card (σ 0) (σ 1)).symm
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by simp))

theorem card_parisiOverlapValues_le_two_mul (N : ℕ) :
    (parisiOverlapValues N).card ≤ 2 * N + 1 :=
  (card_parisiOverlapValues_le N).trans (by omega)

/-- The exact overlap constraints partition the physical spin pairs. -/
theorem sum_constraintR_parisiOverlapValues (N : ℕ) (σ : Fin 2 → Config N) :
    ∑ u ∈ parisiOverlapValues N, constraintR N u σ = 1 := by
  classical
  simp [constraintR, eq_comm, overlap_mem_parisiOverlapValues σ]

end SpinGlass
