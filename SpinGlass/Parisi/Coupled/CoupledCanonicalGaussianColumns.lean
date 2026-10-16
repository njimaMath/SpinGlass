import SpinGlass.Parisi.Coupled.CoupledCanonicalCompressedPath
import SpinGlass.Parisi.Coupled.CoupledGaussianPairLaw

/-!
# Concrete Gaussian columns of the compressed canonical cascade

Independent standard Gaussian columns encode all root pieces and reserve
two columns for each positive level. Driven and auxiliary columns are
disjoint. Their exact covariance and joint-law identities hold when a
driven, auxiliary or total variance vanishes.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

noncomputable def canonicalRootColumn {I : Type*} (vs : I → ℝ≥0)
    (K : I → Fin 2 → Fin 2 → ℝ) (l : Fin 2) : Fin 2 ⊕ (I × Fin 2) → ℝ
  | .inl _ => 0
  | .inr (i, j) => Real.sqrt (vs i : ℝ) * K i l j

noncomputable def canonicalPositiveColumn {I : Type*} (v : ℝ≥0)
    (K : Fin 2 → Fin 2 → ℝ) (l : Fin 2) : Fin 2 ⊕ (I × Fin 2) → ℝ
  | .inl j => Real.sqrt (v : ℝ) * K l j
  | .inr _ => 0

def canonicalLeftColumn {J : Type*} (A : Fin 2 → J → ℝ) (l : Fin 2) : J ⊕ J → ℝ :=
  Sum.elim (A l) 0

def canonicalRightColumn {J : Type*} (A : Fin 2 → J → ℝ) (l : Fin 2) : J ⊕ J → ℝ :=
  Sum.elim 0 (A l)

theorem sqrt_mul_mul_sqrt_eq_nnreal_mul (v : ℝ≥0) (a b : ℝ) :
    (Real.sqrt (v : ℝ) * a) * (Real.sqrt (v : ℝ) * b) = (v : ℝ) * (a * b) := by
  calc
    _ = Real.sqrt (v : ℝ) ^ (2 : ℕ) * (a * b) := by ring
    _ = _ := congrArg (fun c : ℝ => c * (a * b)) (Real.sq_sqrt v.coe_nonneg)

theorem gram_canonicalRootColumn {I : Type*} [Fintype I]
    (vs : I → ℝ≥0) (K : I → Fin 2 → Fin 2 → ℝ) (l l' : Fin 2) :
    gram (canonicalRootColumn vs K) l l' = ∑ i, (vs i : ℝ) * gram (K i) l l' := by
  simp only [gram, Fintype.sum_sum_type, canonicalRootColumn, zero_mul,
    Finset.sum_const_zero, zero_add, Fintype.sum_prod_type,
    sqrt_mul_mul_sqrt_eq_nnreal_mul, Finset.mul_sum]

theorem gram_canonicalPositiveColumn {I : Type*} [Fintype I]
    (v : ℝ≥0) (K : Fin 2 → Fin 2 → ℝ) (l l' : Fin 2) :
    gram (canonicalPositiveColumn (I := I) v K) l l' = (v : ℝ) * gram K l l' := by
  simp only [gram, Fintype.sum_sum_type, canonicalPositiveColumn, zero_mul,
    Finset.sum_const_zero, add_zero, sqrt_mul_mul_sqrt_eq_nnreal_mul, Finset.mul_sum]

theorem gram_canonicalLeftColumn {J : Type*} [Fintype J]
    (A : Fin 2 → J → ℝ) (l l' : Fin 2) :
    gram (canonicalLeftColumn A) l l' = gram A l l' := by
  simp [gram, canonicalLeftColumn, Fintype.sum_sum_type]

theorem gram_canonicalRightColumn {J : Type*} [Fintype J]
    (A : Fin 2 → J → ℝ) (l l' : Fin 2) :
    gram (canonicalRightColumn A) l l' = gram A l l' := by
  simp [gram, canonicalRightColumn, Fintype.sum_sum_type]

theorem gram_canonicalLeft_add_right {J : Type*} [Fintype J]
    (A B : Fin 2 → J → ℝ) (l l' : Fin 2) :
    gram (canonicalLeftColumn A + canonicalRightColumn B) l l' =
      gram A l l' + gram B l l' := by
  simp [gram, canonicalLeftColumn, canonicalRightColumn, Fintype.sum_sum_type]

def canonicalDrivenColumns (J : Type*) [Fintype J] : Finset (J ⊕ J) :=
  Finset.univ.filter fun j => j.isLeft = true

theorem canonicalLeftColumn_zero_of_not_mem {J : Type*} [Fintype J]
    (A : Fin 2 → J → ℝ) (l : Fin 2) (j : J ⊕ J)
    (hj : j ∉ canonicalDrivenColumns J) : canonicalLeftColumn A l j = 0 := by
  cases j with
  | inl j => exact (hj (by simp [canonicalDrivenColumns])).elim
  | inr j => rfl

theorem canonicalRightColumn_zero_of_mem {J : Type*} [Fintype J]
    (A : Fin 2 → J → ℝ) (l : Fin 2) (j : J ⊕ J)
    (hj : j ∈ canonicalDrivenColumns J) : canonicalRightColumn A l j = 0 := by
  cases j with
  | inl j => rfl
  | inr j => simp [canonicalDrivenColumns] at hj

/-- The aggregate standard columns have exactly the joint law of
the actual independent root marks with their total variances. -/
theorem map_gaussian_canonicalRootColumns_eq {I : Type*} [Fintype I]
    (ds es : I → ℝ≥0) (K : I → Fin 2 → Fin 2 → ℝ) :
    (Measure.pi (fun _ : (Fin 2 ⊕ (I × Fin 2)) ⊕ (Fin 2 ⊕ (I × Fin 2)) => gaussianReal 0 1)).map
      (fun z => WithLp.toLp 2 (fun l => ∑ j,
        (canonicalLeftColumn (canonicalRootColumn ds K) +
          canonicalRightColumn (canonicalRootColumn es K)) l j * z j)) =
      (Measure.pi (fun j : I × Fin 2 => gaussianReal 0 (ds j.1 + es j.1))).map
        (fun z => WithLp.toLp 2 (fun l => ∑ j : I × Fin 2, K j.1 l j.2 * z j)) := by
  classical
  apply map_pi_gaussianReal_linear_eq_of_covariance
  intro l l'
  simp only [NNReal.coe_one, one_mul]
  change gram (canonicalLeftColumn (canonicalRootColumn ds K) +
    canonicalRightColumn (canonicalRootColumn es K)) l l' = _
  rw [gram_canonicalLeft_add_right, gram_canonicalRootColumn, gram_canonicalRootColumn,
    ← Finset.sum_add_distrib]
  simp only [Fintype.sum_prod_type, NNReal.coe_add]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← add_mul, gram, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

theorem map_gaussian_canonicalPositiveColumns_eq {I : Type*} [Fintype I]
    (d e : ℝ≥0) (K : Fin 2 → Fin 2 → ℝ) :
    (Measure.pi (fun _ : (Fin 2 ⊕ (I × Fin 2)) ⊕ (Fin 2 ⊕ (I × Fin 2)) => gaussianReal 0 1)).map
      (fun z => WithLp.toLp 2 (fun l => ∑ j,
        (canonicalLeftColumn (canonicalPositiveColumn (I := I) d K) +
          canonicalRightColumn (canonicalPositiveColumn (I := I) e K)) l j * z j)) =
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 (d + e))).map
        (fun z => WithLp.toLp 2 (fun l => ∑ j : Fin 2, K l j * z j)) := by
  classical
  apply map_pi_gaussianReal_linear_eq_of_covariance
  intro l l'
  simp only [NNReal.coe_one, one_mul]
  change gram (canonicalLeftColumn (canonicalPositiveColumn (I := I) d K) +
    canonicalRightColumn (canonicalPositiveColumn (I := I) e K)) l l' = _
  rw [gram_canonicalLeft_add_right, gram_canonicalPositiveColumn, gram_canonicalPositiveColumn,
    ← add_mul]
  simp only [NNReal.coe_add, gram, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

abbrev ParisiCanonicalColumnHalf {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) :=
  Fin 2 ⊕ (Fin (parisiCanonicalRootPieces ms r p).length × Fin 2)

abbrev ParisiCanonicalColumns {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) :=
  ParisiCanonicalColumnHalf ms r p ⊕ ParisiCanonicalColumnHalf ms r p

noncomputable def parisiCanonicalDrivenRootFactor {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) : Fin 2 → ParisiCanonicalColumns ms r p → ℝ :=
  canonicalLeftColumn (canonicalRootColumn
    (fun i => ((parisiCanonicalRootPieces ms r p)[i.val]).drivenVariance ξ qs p t u)
    (fun i => ((parisiCanonicalRootPieces ms r p)[i.val]).gaussianFactor negative r p))

noncomputable def parisiCanonicalAuxiliaryRootFactor {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) : Fin 2 → ParisiCanonicalColumns ms r p → ℝ :=
  canonicalRightColumn (canonicalRootColumn
    (fun i => ((parisiCanonicalRootPieces ms r p)[i.val]).auxiliaryVariance ξ qs p t u)
    (fun i => ((parisiCanonicalRootPieces ms r p)[i.val]).gaussianFactor negative r p))

noncomputable def parisiCanonicalDrivenFactor {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ)
    (i : Fin (parisiCanonicalPositivePieces ms r p).length) :
    Fin 2 → ParisiCanonicalColumns ms r p → ℝ :=
  canonicalLeftColumn (canonicalPositiveColumn
    (((parisiCanonicalPositivePieces ms r p)[i.val]).drivenVariance ξ qs p t u)
    (((parisiCanonicalPositivePieces ms r p)[i.val]).gaussianFactor negative r p))

noncomputable def parisiCanonicalAuxiliaryFactor {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ)
    (i : Fin (parisiCanonicalPositivePieces ms r p).length) :
    Fin 2 → ParisiCanonicalColumns ms r p → ℝ :=
  canonicalRightColumn (canonicalPositiveColumn
    (((parisiCanonicalPositivePieces ms r p)[i.val]).auxiliaryVariance ξ qs p t u)
    (((parisiCanonicalPositivePieces ms r p)[i.val]).gaussianFactor negative r p))

theorem gram_parisiCanonicalDrivenRootFactor {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {t u : ℝ} (ht : 0 ≤ t)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) (l l' : Fin 2) :
    gram (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u) l l' =
      deriv (parisiTimeProfile ξ t) (parisiCanonicalCompressedRho ms qs negative r p u l l' 1) -
        deriv (parisiTimeProfile ξ t) (parisiCanonicalCompressedRho ms qs negative r p u l l' 0) := by
  rw [parisiCanonicalDrivenRootFactor, gram_canonicalLeftColumn, gram_canonicalRootColumn]
  exact sum_parisiCanonicalRootDrivenVariance_mul_gram hξ ms qs hm hq negative r p ht hu l l'

theorem gram_parisiCanonicalDrivenFactor {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {t u : ℝ} (ht : 0 ≤ t)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)))
    (i : Fin (parisiCanonicalPositivePieces ms r p).length) (l l' : Fin 2) :
    gram (parisiCanonicalDrivenFactor ξ ms qs negative r p t u i) l l' =
      deriv (parisiTimeProfile ξ t)
          (parisiCanonicalCompressedRho ms qs negative r p u l l' (i.val + 2)) -
        deriv (parisiTimeProfile ξ t)
          (parisiCanonicalCompressedRho ms qs negative r p u l l' (i.val + 1)) := by
  rw [parisiCanonicalDrivenFactor, gram_canonicalLeftColumn, gram_canonicalPositiveColumn]
  exact parisiCanonicalPositiveDrivenVariance_mul_gram hξ ms qs hm hq negative r p ht hu i l l'

/-- The concrete aggregate root has the actual product-coordinate
Gaussian law, with no covariance or law identity supplied as a hypothesis. -/
theorem map_gaussian_parisiCanonicalRootFactors_eq {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) :
    (Measure.pi (fun _ : ParisiCanonicalColumns ms r p => gaussianReal 0 1)).map
      (fun z => WithLp.toLp 2 (fun l => ∑ j,
        (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u +
          parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u) l j * z j)) =
      (Measure.pi (fun j : Fin (parisiCanonicalRootPieces ms r p).length × Fin 2 =>
        gaussianReal 0 (((parisiCanonicalRootPieces ms r p)[j.1.val]).variance ξ qs p t u))).map
        (fun z => WithLp.toLp 2 (fun l => ∑ j,
          ((parisiCanonicalRootPieces ms r p)[j.1.val]).gaussianFactor negative r p l j.2 * z j)) := by
  have he := map_gaussian_canonicalRootColumns_eq
    (I := Fin (parisiCanonicalRootPieces ms r p).length)
    (fun i => ((parisiCanonicalRootPieces ms r p)[i.val]).drivenVariance ξ qs p t u)
    (fun i => ((parisiCanonicalRootPieces ms r p)[i.val]).auxiliaryVariance ξ qs p t u)
    (fun i => ((parisiCanonicalRootPieces ms r p)[i.val]).gaussianFactor negative r p)
  simpa only [parisiCanonicalDrivenRootFactor, parisiCanonicalAuxiliaryRootFactor,
    ParisiCanonicalPiece.drivenVariance_add_auxiliaryVariance] using he

theorem map_gaussian_parisiCanonicalPositiveFactors_eq {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ)
    (i : Fin (parisiCanonicalPositivePieces ms r p).length) :
    (Measure.pi (fun _ : ParisiCanonicalColumns ms r p => gaussianReal 0 1)).map
      (fun z => WithLp.toLp 2 (fun l => ∑ j,
        (parisiCanonicalDrivenFactor ξ ms qs negative r p t u i +
          parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u i) l j * z j)) =
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0
        (((parisiCanonicalPositivePieces ms r p)[i.val]).variance ξ qs p t u))).map
        (fun z => WithLp.toLp 2 (fun l => ∑ j,
          ((parisiCanonicalPositivePieces ms r p)[i.val]).gaussianFactor negative r p l j * z j)) := by
  have he := map_gaussian_canonicalPositiveColumns_eq
    (I := Fin (parisiCanonicalRootPieces ms r p).length)
    (((parisiCanonicalPositivePieces ms r p)[i.val]).drivenVariance ξ qs p t u)
    (((parisiCanonicalPositivePieces ms r p)[i.val]).auxiliaryVariance ξ qs p t u)
    (((parisiCanonicalPositivePieces ms r p)[i.val]).gaussianFactor negative r p)
  simpa only [parisiCanonicalDrivenFactor, parisiCanonicalAuxiliaryFactor,
    ParisiCanonicalPiece.drivenVariance_add_auxiliaryVariance] using he

end SpinGlass
