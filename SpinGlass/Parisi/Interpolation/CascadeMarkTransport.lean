import SpinGlass.Parisi.Interpolation.PairFractionIntegral

/-!
# Transporting every mark of a cascade

Coordinate maps act on the actual independent mark arrays and preserve
their product laws. Branch expansions then transport both the partition
and the constrained prefix numerator, including noninvertible maps.
-/

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators

namespace ProbabilityTheory

noncomputable section

universe u v

variable {T : Type u} {T' : Type v}

def cascadeMarksMap : (k : ℕ) → (Fin k → T → T') → CascadeMarks T k → CascadeMarks T' k
  | 0, _, _ => PUnit.unit
  | k + 1, φ, z =>
    (fun n j => φ 0 (z.1 n j), fun n j => cascadeMarksMap k (Fin.tail φ) (z.2 n j))

theorem branchMarks_cascadeMarksMap (k : ℕ) (φ : Fin k → T → T')
    (z : CascadeMarks T k) (α : Fin k → ℕ × ℕ) :
    branchMarks k (cascadeMarksMap k φ z) α = fun p => φ p (branchMarks k z α p) := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    funext p
    refine Fin.cases ?_ (fun j => ?_) p
    · rfl
    · exact congrFun (ih (Fin.tail φ) (z.2 (α 0).1 (α 0).2) (Fin.tail α)) j

variable [MeasurableSpace T] [MeasurableSpace T']

theorem measurable_cascadeMarksMap (k : ℕ) (φ : Fin k → T → T')
    (hφ : ∀ p, Measurable (φ p)) : Measurable (cascadeMarksMap k φ) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ fun n => measurable_pi_lambda _ fun j =>
        (hφ 0).comp ((measurable_pi_apply j).comp ((measurable_pi_apply n).comp measurable_fst))
    · exact measurable_pi_lambda _ fun n => measurable_pi_lambda _ fun j =>
        (ih (Fin.tail φ) (fun p => hφ p.succ)).comp
          ((measurable_pi_apply j).comp ((measurable_pi_apply n).comp measurable_snd))

private theorem measurePreserving_iidArray {μ : Measure T} {ν : Measure T'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : T → T'}
    (hf : MeasurePreserving f μ ν) :
    MeasurePreserving (fun z : ℕ → ℕ → T => fun n j => f (z n j))
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => μ)
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => ν) := by
  have hrow : Measurable (fun z : ℕ → T => fun j => f (z j)) :=
    measurable_pi_lambda _ fun j => hf.measurable.comp (measurable_pi_apply j)
  refine ⟨measurable_pi_lambda _ fun n => hrow.comp (measurable_pi_apply n), ?_⟩
  rw [Measure.infinitePi_map_pi _ (fun _ => hrow)]
  simp_rw [Measure.infinitePi_map_pi _ (fun _ => hf.measurable), hf.map_eq]

/-- Coordinatewise transport of the actual cascade mark law. No
injectivity or positive variance is required. -/
theorem measurePreserving_cascadeMarksMap (k : ℕ)
    (μs : Fin k → Measure T) (νs : Fin k → Measure T')
    [∀ p, IsProbabilityMeasure (μs p)] [∀ p, IsProbabilityMeasure (νs p)]
    (φ : Fin k → T → T') (hφ : ∀ p, MeasurePreserving (φ p) (μs p) (νs p)) :
    MeasurePreserving (cascadeMarksMap k φ) (cascadeMarksLaw k μs) (cascadeMarksLaw k νs) := by
  induction k with
  | zero =>
    refine ⟨measurable_const, ?_⟩
    simp [cascadeMarksLaw_zero, cascadeMarksMap]
  | succ k ih =>
    exact (measurePreserving_iidArray (hφ 0)).prod
      (measurePreserving_iidArray (ih (Fin.tail μs) (Fin.tail νs) (Fin.tail φ)
        (fun p => hφ p.succ)))

theorem cascadeSum_cascadeMarksMap (k : ℕ) (φ : Fin k → T → T')
    (hφ : ∀ p, Measurable (φ p)) {G : (Fin k → T') → ℝ≥0∞} (hG : Measurable G)
    (w : CascadeWeights k) (z : CascadeMarks T k) :
    cascadeSum k G (cascadeZip k (w, cascadeMarksMap k φ z)) =
      cascadeSum k (fun x => G (fun p => φ p (x p))) (cascadeZip k (w, z)) := by
  have hm : Measurable (fun x : Fin k → T => fun p => φ p (x p)) :=
    measurable_pi_lambda _ fun p => (hφ p).comp (measurable_pi_apply p)
  rw [cascadeSum_cascadeZip k hG, cascadeSum_cascadeZip k
    (G := fun x => G (fun p => φ p (x p))) (hG.comp hm)]
  simp_rw [branchMarks_cascadeMarksMap]

theorem cascadeSqPair_cascadeMarksMap (k r : ℕ) (φ : Fin k → T → T')
    (hφ : ∀ p, Measurable (φ p)) {U : (Fin k → T' × T') → ℝ≥0∞} (hU : Measurable U)
    (w : CascadeWeights k) (z : CascadeMarks T k) :
    cascadeSqPair k r U (cascadeZip k (w, cascadeMarksMap k φ z)) =
      cascadeSqPair k r (fun x => U (fun p => (φ p (x p).1, φ p (x p).2)))
        (cascadeZip k (w, z)) := by
  have hm : Measurable (fun x : Fin k → T × T => fun p => (φ p (x p).1, φ p (x p).2)) :=
    measurable_pi_lambda _ fun p =>
      ((hφ p).comp (measurable_pi_apply p).fst).prodMk
        ((hφ p).comp (measurable_pi_apply p).snd)
  rw [cascadeSqPair_cascadeZip k r hU, cascadeSqPair_cascadeZip k r
    (U := fun x => U (fun p => (φ p (x p).1, φ p (x p).2))) (hU.comp hm)]
  simp_rw [branchMarks_cascadeMarksMap]

end

end ProbabilityTheory

namespace SpinGlass

noncomputable section

universe u v

variable {T : Type u} {T' : Type v} [MeasurableSpace T] [MeasurableSpace T']

theorem cascadePairObservable_cascadeMarksMap (k r : ℕ) (φ : Fin k → T → T')
    (hφ : ∀ p, Measurable (φ p)) {U : (Fin k → T' × T') → ℝ≥0∞}
    {G : (Fin k → T') → ℝ≥0∞} (hU : Measurable U) (hG : Measurable G)
    (w : CascadeWeights k) (z : CascadeMarks T k) :
    cascadePairObservable k r U G w (cascadeMarksMap k φ z) =
      cascadePairObservable k r (fun x => U (fun p => (φ p (x p).1, φ p (x p).2)))
        (fun x => G (fun p => φ p (x p))) w z := by
  unfold cascadePairObservable
  rw [cascadeSum_cascadeMarksMap k φ hφ hG, cascadeSqPair_cascadeMarksMap k r φ hφ hU]

end

end SpinGlass
