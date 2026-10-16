import SpinGlass.Parisi.Coupled.CoupledCanonicalAuxiliaryProjection
import SpinGlass.Parisi.Coupled.CoupledCascadeListDeletion

/-!
# Actual auxiliary marks from the canonical standard columns

Projection and square-root rescaling identify the physical auxiliary law,
including zero variances. The aggregate root has one surviving auxiliary
coordinate, whereas all positive layers use their reserved two columns.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable def canonicalScaledMarksMap {S D : Type*} (v : ℝ≥0)
    (index : Fin 2 → D) (z : S × D → ℝ) : S × Fin 2 → ℝ :=
  fun q => Real.sqrt (v : ℝ) * z (q.1, index q.2)

theorem measurable_canonicalScaledMarksMap {S D : Type*} (v : ℝ≥0)
    (index : Fin 2 → D) : Measurable (canonicalScaledMarksMap (S := S) v index) := by
  unfold canonicalScaledMarksMap
  fun_prop

/-- Injective coordinate projection retains independence across sites;
square-root rescaling gives the exact variance, also at variance zero. -/
theorem map_pi_gaussianReal_canonicalScaledMarksMap {S D : Type*} [Fintype S] [Fintype D]
    (v : ℝ≥0) (index : Fin 2 → D) (hinj : Function.Injective index) :
    (Measure.pi (fun _ : S × D => gaussianReal 0 1)).map
      (canonicalScaledMarksMap v index) =
      Measure.pi (fun _ : S × Fin 2 => gaussianReal 0 v) := by
  classical
  let proj := fun z : S × D → ℝ => fun q : S × Fin 2 => z (q.1, index q.2)
  have hp : Measurable proj := by fun_prop
  have hi : Function.Injective (fun q : S × Fin 2 => (q.1, index q.2)) := by
    intro x y h
    exact Prod.ext (congrArg (Prod.fst : S × D → S) h)
      (hinj (congrArg (Prod.snd : S × D → D) h))
  have hproj : (Measure.pi (fun _ : S × D => gaussianReal 0 1)).map proj =
      Measure.pi (fun _ : S × Fin 2 => gaussianReal 0 1) := by
    simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_comp_injective (fun _ : S × D => gaussianReal 0 1) hi
  change ((Measure.pi (fun _ : S × D => gaussianReal 0 1)).map
    ((fun z : S × Fin 2 → ℝ => fun q => Real.sqrt (v : ℝ) * z q) ∘ proj)) = _
  rw [← Measure.map_map (by fun_prop) hp, hproj,
    Measure.pi_map_pi (fun _ => (show Measurable (fun z : ℝ => Real.sqrt (v : ℝ) * z) by
      fun_prop).aemeasurable)]
  congr 1
  funext q
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.eq
  change Real.sqrt (v : ℝ) ^ 2 * 1 = (v : ℝ)
  simp [Real.sq_sqrt v.coe_nonneg]

theorem sum_canonicalAuxiliaryPositiveColumn_mul {I S : Type*} [Fintype I]
    (v : ℝ≥0) (K : Fin 2 → Fin 2 → ℝ)
    (z : S × ((Fin 2 ⊕ (I × Fin 2)) ⊕ (Fin 2 ⊕ (I × Fin 2))) → ℝ)
    (l : Fin 2) (s : S) :
    (∑ j, canonicalRightColumn (canonicalPositiveColumn (I := I) v K) l j * z (s, j)) =
      ∑ j, K l j * canonicalScaledMarksMap v (fun j => .inr (.inl j)) z (s, j) := by
  simp only [canonicalRightColumn, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, canonicalPositiveColumn,
    canonicalScaledMarksMap, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def parisiCanonicalAuxiliaryPieceFactor {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) (e : ParisiCanonicalPiece k) :
    Fin 2 → ParisiCanonicalColumns ms r p → ℝ :=
  canonicalRightColumn (canonicalPositiveColumn
    (e.auxiliaryVariance ξ qs p t u) (e.gaussianFactor negative r p))

theorem parisiCanonicalAuxiliaryPieceFactor_eq_zero {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) (e : ParisiCanonicalPiece k)
    (he : e.isAuxiliary = false) :
    parisiCanonicalAuxiliaryPieceFactor ξ ms qs negative r p t u e = 0 := by
  have hz := e.auxiliaryVariance_eq_zero_of_not_auxiliary ξ qs p t u he
  funext l j
  cases j with
  | inl j => rfl
  | inr j =>
    cases j <;> simp [parisiCanonicalAuxiliaryPieceFactor, canonicalRightColumn,
      canonicalPositiveColumn, hz]

noncomputable def parisiCanonicalAuxiliaryRootIndex {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms) (r : Fin (k + 1)) (p : Fin (k + 2)) :
    Fin (parisiCanonicalRootPieces ms r p).length :=
  ⟨0, lt_of_lt_of_le (by norm_num : 0 < 2)
    (parisiCanonicalRootPieces_length_ge_two ms hm r p)⟩

noncomputable def parisiCanonicalAuxiliaryRootMarksMap {N k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t : ℝ)
    (z : Fin N × ParisiCanonicalColumns ms r p → ℝ) : Fin N × Fin 2 → ℝ :=
  canonicalScaledMarksMap (parisiAuxRootVar ξ qs t)
    (fun j => .inr (.inr (parisiCanonicalAuxiliaryRootIndex ms hm r p, j))) z

theorem measurable_parisiCanonicalAuxiliaryRootMarksMap {N k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t : ℝ) :
    Measurable (parisiCanonicalAuxiliaryRootMarksMap (N := N) ξ ms qs hm r p t) :=
  measurable_canonicalScaledMarksMap _ _

theorem map_gaussian_parisiCanonicalAuxiliaryRootMarksMap {N k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t : ℝ) :
    (rootMarksLaw N (J := ParisiCanonicalColumns ms r p) 1).map
      (parisiCanonicalAuxiliaryRootMarksMap ξ ms qs hm r p t) =
      rootMarksLaw N (J := Fin 2) (parisiAuxRootVar ξ qs t) := by
  unfold parisiCanonicalAuxiliaryRootMarksMap rootMarksLaw
  apply map_pi_gaussianReal_canonicalScaledMarksMap
  intro x y h
  exact congrArg Prod.snd (Sum.inr.inj (Sum.inr.inj h))

/-- The aggregate root field reads just the old auxiliary root mark. -/
theorem sum_parisiCanonicalAuxiliaryRootFactor_mul {N k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ)
    (z : Fin N × ParisiCanonicalColumns ms r p → ℝ) (l : Fin 2) (s : Fin N) :
    (∑ j, parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u l j * z (s, j)) =
      ∑ j, couplingFactorSgn 1 (r.val + 1) 0 l j *
        parisiCanonicalAuxiliaryRootMarksMap ξ ms qs hm r p t z (s, j) := by
  classical
  let i₀ := parisiCanonicalAuxiliaryRootIndex ms hm r p
  have hi₀ : i₀.val = 0 := rfl
  have he₀ : (parisiCanonicalRootPieces ms r p)[i₀.val] = .auxiliary 0 := by
    obtain ⟨tail, htail⟩ := parisiCanonicalRootPieces_auxiliary_prefix ms hm r p
    simp [htail, hi₀]
  simp only [parisiCanonicalAuxiliaryRootFactor, canonicalRightColumn, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
    canonicalRootColumn, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i₀]
  · simp only [he₀, parisiCanonicalAuxiliary_gaussianFactor]
    simp only [ParisiCanonicalPiece.auxiliaryVariance, ParisiCanonicalPiece.isDriven,
      Bool.false_eq_true, ite_false, ParisiCanonicalPiece.variance, parisiAllVars,
      Fin.val_zero, parisiCanonicalAuxiliaryRootMarksMap, canonicalScaledMarksMap,
      parisiAuxRootVar]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro i _hi hne
    have hi : i.val ≠ 0 := by intro hz; exact hne (Fin.ext (hz.trans hi₀.symm))
    have ha : ((parisiCanonicalRootPieces ms r p)[i.val]).isAuxiliary = false :=
      Bool.eq_false_iff.2 (fun h => hi
        ((parisiCanonicalRootPieces_isAuxiliary_iff ms hm r p i).1 h))
    have hv := ParisiCanonicalPiece.auxiliaryVariance_eq_zero_of_not_auxiliary
      ξ qs p t u ((parisiCanonicalRootPieces ms r p)[i.val]) ha
    simp [hv]
  · simp

end SpinGlass
