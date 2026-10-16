import SpinGlass.Parisi.Coupled.CoupledCascadeDeletion

/-!
# Deleting marks with zero additive contribution

Positive-mass layers whose contribution is identically zero are identities
under a probability mark law. Filtering these layers preserves every
remaining index in order. No ordering or integrability assumption is needed.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- A finite additive cascade is unchanged by deleting every layer
with identically zero contribution and nonzero mass. In particular, this
does not apply the positive-mass cascade operation at a zero root mass. -/
theorem cascadeRec_additive_list_filter_zero {α E T : Type*}
    [AddCommMonoid E] [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (mass : α → ℝ)
    (shift : α → T → E) (test : α → Bool) (l : List α)
    (hzero : ∀ e ∈ l, test e = false → ∀ z, shift e z = 0)
    (hmass : ∀ e ∈ l, test e = false → mass e ≠ 0)
    (F : E → ℝ≥0∞) (s : E) :
    cascadeRec l.length (fun i => mass (l.get i)) (fun _ => μ)
      (fun zs => F (s + ∑ i, shift (l.get i) (zs i))) =
    cascadeRec (l.filter test).length
      (fun i => mass ((l.filter test).get i)) (fun _ => μ)
      (fun zs => F (s + ∑ i, shift ((l.filter test).get i) (zs i))) := by
  classical
  induction l generalizing s with
  | nil => rfl
  | cons e l ih =>
    have hz : ∀ a ∈ l, test a = false → ∀ z, shift a z = 0 :=
      fun a ha => hzero a (List.mem_cons_of_mem _ ha)
    have hm : ∀ a ∈ l, test a = false → mass a ≠ 0 :=
      fun a ha => hmass a (List.mem_cons_of_mem _ ha)
    have hsplit (z : T) :
        (fun zs : Fin l.length → T =>
          F (s + ∑ i : Fin (e :: l).length,
            shift ((e :: l).get i) ((Fin.cons z zs : Fin (l.length + 1) → T) i))) =
        fun zs => F ((s + shift e z) + ∑ i, shift (l.get i) (zs i)) := by
      funext zs
      simp only [List.length_cons, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_zero, Fin.val_succ,
        List.get_eq_getElem, add_assoc]
    simp only [List.length_cons]
    rw [cascadeRec_succ]
    change (∫⁻ z, cascadeRec l.length (fun i => mass (l.get i)) (fun _ => μ)
      (fun zs : Fin l.length → T => F (s + ∑ i : Fin (e :: l).length,
        shift ((e :: l).get i) ((Fin.cons z zs : Fin (l.length + 1) → T) i))) ^
          mass e ∂μ) ^ (1 / mass e) = _
    simp_rw [hsplit, ih hz hm]
    cases ht : test e with
    | false =>
      rw [show (e :: l).filter test = l.filter test by simp [ht]]
      simp_rw [hzero e List.mem_cons_self ht, add_zero]
      rw [lintegral_const, measure_univ, mul_one, ← ENNReal.rpow_mul,
        mul_one_div_cancel (hmass e List.mem_cons_self ht), ENNReal.rpow_one]
    | true =>
      rw [show (e :: l).filter test = e :: l.filter test by simp [ht]]
      simp only [List.length_cons]
      rw [cascadeRec_succ]
      congr 1
      apply lintegral_congr
      intro z
      congr 1
      congr 1
      funext zs
      simp only [List.length_cons, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_zero, Fin.val_succ,
        List.get_eq_getElem, add_assoc]

/-- All branch marks can be absorbed into the realized site field
before taking a cascade or a disorder expectation. -/
theorem pairHamG_eq_additiveSiteField {N k : ℕ} {J : Type*} [Fintype J]
    (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ)
    (zs : Fin k → Fin N × J → ℝ) :
    pairHamG N k c H lam a K₀ K z₀ zs =
      pairHamG N 0 c H lam
        (fun q => (a q + ∑ j, K₀ q.2 j * z₀ (q.1, j)) +
          ∑ i, ∑ j, K i q.2 j * zs i (q.1, j))
        (0 : Fin 2 → J → ℝ) Fin.elim0 0 Fin.elim0 := by
  unfold pairHamG pairBranchZX pairBranchHamX pairBranchMark
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, Fin.sum_univ_zero,
    add_zero, add_assoc]

/-- Deleting all zero-factor layers from a paired constrained partition
function is exact under any common probability mark law. -/
theorem cascadeRec_pairHamG_list_filter_zero {α : Type*} {N : ℕ}
    {J : Type*} [Fintype J] (μ : Measure (Fin N × J → ℝ))
    [IsProbabilityMeasure μ] (mass : α → ℝ) (K : α → Fin 2 → J → ℝ)
    (test : α → Bool) (l : List α)
    (hzero : ∀ e ∈ l, test e = false → K e = 0)
    (hmass : ∀ e ∈ l, test e = false → mass e ≠ 0)
    (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) :
    cascadeRec l.length (fun i => mass (l.get i)) (fun _ => μ)
      (pairHamG N l.length c H lam a K₀ (fun i => K (l.get i)) z₀) =
    cascadeRec (l.filter test).length
      (fun i => mass ((l.filter test).get i)) (fun _ => μ)
      (pairHamG N (l.filter test).length c H lam a K₀
        (fun i => K ((l.filter test).get i)) z₀) := by
  let shift (e : α) (z : Fin N × J → ℝ) : Fin N × Fin 2 → ℝ :=
    fun q => ∑ j, K e q.2 j * z (q.1, j)
  let s : Fin N × Fin 2 → ℝ := fun q => a q + ∑ j, K₀ q.2 j * z₀ (q.1, j)
  let F (b : Fin N × Fin 2 → ℝ) :=
    pairHamG N 0 c H lam b (0 : Fin 2 → J → ℝ) Fin.elim0 0 Fin.elim0
  have hz : ∀ e ∈ l, test e = false → ∀ z, shift e z = 0 := by
    intro e he ht z
    funext q
    simp [shift, hzero e he ht]
  have hf := cascadeRec_additive_list_filter_zero μ mass shift test l hz hmass F s
  have hleft : pairHamG N l.length c H lam a K₀ (fun i => K (l.get i)) z₀ =
      fun zs : Fin l.length → Fin N × J → ℝ =>
        F (s + ∑ i : Fin l.length, shift (l.get i) (zs i)) := by
    funext zs
    rw [pairHamG_eq_additiveSiteField]
    change F _ = F _
    congr 1
    funext q
    simp only [s, shift, Pi.add_apply, Finset.sum_apply]
  have hright : pairHamG N (l.filter test).length c H lam a K₀
      (fun i => K ((l.filter test).get i)) z₀ =
      fun zs : Fin (l.filter test).length → Fin N × J → ℝ =>
        F (s + ∑ i : Fin (l.filter test).length, shift ((l.filter test).get i) (zs i)) := by
    funext zs
    rw [pairHamG_eq_additiveSiteField]
    change F _ = F _
    congr 1
    funext q
    simp only [s, shift, Pi.add_apply, Finset.sum_apply]
  rw [hleft, hright]
  exact hf

/-- Evaluating a labelled tuple as its `ofFn` list leaves the actual
paired cascade unchanged, with its dependent length transported exactly. -/
theorem cascadeRec_pairHamG_ofFn {α : Type*} {N k : ℕ} {J : Type*} [Fintype J]
    (μ : Measure (Fin N × J → ℝ)) (mass : α → ℝ) (K : α → Fin 2 → J → ℝ)
    (f : Fin k → α) (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) :
    cascadeRec (List.ofFn f).length (fun i => mass ((List.ofFn f).get i)) (fun _ => μ)
      (pairHamG N (List.ofFn f).length c H lam a K₀ (fun i => K ((List.ofFn f).get i)) z₀) =
      cascadeRec k (fun i => mass (f i)) (fun _ => μ)
        (pairHamG N k c H lam a K₀ (fun i => K (f i)) z₀) := by
  let F (p : Σ n : ℕ, Fin n → α) := cascadeRec p.1 (fun i => mass (p.2 i)) (fun _ => μ)
    (pairHamG N p.1 c H lam a K₀ (fun i => K (p.2 i)) z₀)
  have hl : (⟨(List.ofFn f).length, (List.ofFn f).get⟩ : Σ n : ℕ, Fin n → α) = ⟨k, f⟩ :=
    Fin.sigma_eq_of_eq_comp_cast List.length_ofFn (funext fun i => List.get_ofFn f i)
  exact congrArg F hl

end SpinGlass
