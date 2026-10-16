import SpinGlass.Parisi.Concentration.CascadePairBounds
import Common.Mathlib.Probability.PointProcess.CascadeBranches

/-!
# Constrained pair sums over explicit branches

The recursive pair numerator is the double sum over actual branches.
Unlike the product specialization, this identity retains the joint
observable needed for a physical overlap constraint.
-/

open MeasureTheory Function
open scoped ENNReal

namespace ProbabilityTheory

noncomputable section

universe u

variable {T : Type u} [MeasurableSpace T]

private lemma measurable_lintegral_superCounting_fixed
    {E : Type u} [MeasurableSpace E] (F : E → E → ℝ≥0∞)
    (hF : Measurable (uncurry F)) (ω : SuperSample E) :
    Measurable (fun p => ∫⁻ q, F p q ∂superCounting ω) := by
  have hm : Measurable (fun q : E × SuperSample E =>
      ∫⁻ x, F q.1 x ∂superCounting q.2) :=
    measurable_lintegral_superCounting_prod hF
  have hmap : Measurable (fun p : E => (p, ω)) :=
    measurable_id.prodMk measurable_const
  have hh := hm.comp hmap
  simp only [Function.comp_def] at hh
  exact hh

omit [MeasurableSpace T] in
private lemma pair_fin_cons {k : ℕ} (a b : T) (x y : Fin k → T) :
    (fun p : Fin (k + 1) => ((Fin.cons a x : Fin (k + 1) → T) p,
      (Fin.cons b y : Fin (k + 1) → T) p)) =
      (Fin.cons (a, b) (fun p => (x p, y p)) : Fin (k + 1) → T × T) := by
  funext p
  refine Fin.cases ?_ (fun j => ?_) p <;> rfl

/-- The recursive unconstrained-prefix pair sum keeps an arbitrary joint
branch observable when weights and marks are separated. -/
theorem cascadePairSum_cascadeZip :
    ∀ (k : ℕ) {U : (Fin k → T × T) → ℝ≥0∞}, Measurable U →
      ∀ (w₁ w₂ : CascadeWeights k) (z₁ z₂ : CascadeMarks T k),
      cascadePairSum k U (cascadeZip k (w₁, z₁)) (cascadeZip k (w₂, z₂)) =
        ∑' α : Fin k → ℕ × ℕ, ∑' γ : Fin k → ℕ × ℕ,
          branchWeight k w₁ α * branchWeight k w₂ γ *
            U (fun p => (branchMarks k z₁ α p, branchMarks k z₂ γ p)) := by
  intro k
  induction k with
  | zero =>
    intro U hU w₁ w₂ z₁ z₂
    simp only [cascadePairSum_zero, tsum_fintype, Finset.univ_unique,
      Finset.sum_singleton, branchWeight, one_mul]
    exact congrArg U (Subsingleton.elim _ _)
  | succ k ih =>
    intro U hU w₁ w₂ z₁ z₂
    let F := fun p q : ℝ × (T × CascadeSpace T k) =>
      ENNReal.ofReal p.1 * ENNReal.ofReal q.1 *
        cascadePairSum k (fun x => U (Fin.cons (p.2.1, q.2.1) x)) p.2.2 q.2.2
    have hB := measurable_cascadePairSum_prod k
      (U := fun a : T × T => fun x => U (Fin.cons a x)) (hU.comp measurable_fin_cons)
    have hF : Measurable (Function.uncurry F) := by
      have hh : Measurable (fun v : (ℝ × (T × CascadeSpace T k)) ×
          (ℝ × (T × CascadeSpace T k)) => ((v.1.2.1, v.2.2.1), (v.1.2.2, v.2.2.2))) := by
        fun_prop
      exact ((measurable_fst.fst.ennreal_ofReal).mul
        (measurable_snd.fst.ennreal_ofReal)).mul (hB.comp hh)
    have houter := measurable_lintegral_superCounting_fixed F hF
      (cascadeZip (k + 1) (w₂, z₂))
    have hinner (p : ℝ × (T × CascadeSpace T k)) :
        (∫⁻ q, F p q ∂superCounting (cascadeZip (k + 1) (w₂, z₂))) =
        ∑' nj : ℕ × ℕ, if nj.2 < (w₂.1 nj.1).2 then
          F p ((w₂.1 nj.1).1 nj.2,
            (z₂.1 nj.1 nj.2, cascadeZip k (w₂.2 nj.1 nj.2, z₂.2 nj.1 nj.2))) else 0 := by
      have hm : Measurable (F p) := hF.comp (measurable_const.prodMk measurable_id)
      rw [cascadeZip_succ, lintegral_superCounting_superZip _ _ hm, ← tsum_nat_prod_ite]
    change (∫⁻ p, ∫⁻ q, F p q ∂superCounting (cascadeZip (k + 1) (w₂, z₂))
      ∂superCounting (cascadeZip (k + 1) (w₁, z₁))) = _
    rw [cascadeZip_succ k (w₁, z₁), lintegral_superCounting_superZip _ _ houter,
      ← tsum_nat_prod_ite]
    simp_rw [hinner]
    conv_rhs => simp only [tsum_fin_succ]
    apply tsum_congr
    intro nj₁
    conv_rhs => rw [ENNReal.tsum_comm]
    simp_rw [branchWeight_succ, branchMarks_succ, pair_fin_cons]
    by_cases h₁ : nj₁.2 < (w₁.1 nj₁.1).2
    · simp only [h₁, ite_true]
      apply tsum_congr
      intro nj₂
      by_cases h₂ : nj₂.2 < (w₂.1 nj₂.1).2
      · simp only [h₂, ite_true, F]
        rw [ih (U := fun x => U (Fin.cons (z₁.1 nj₁.1 nj₁.2, z₂.1 nj₂.1 nj₂.2) x))
          (hU.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))]
        simp_rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro β
        apply tsum_congr
        intro δ
        ring
      · simp [h₂]
    · simp [h₁]

/-- The constrained recursive prefix numerator is the actual pair sum
over branches sharing the specified prefix. -/
theorem cascadeSqPair_cascadeZip :
    ∀ (k r : ℕ) {U : (Fin k → T × T) → ℝ≥0∞}, Measurable U →
      ∀ (w : CascadeWeights k) (z : CascadeMarks T k),
      cascadeSqPair k r U (cascadeZip k (w, z)) =
        ∑' α : Fin k → ℕ × ℕ, ∑' γ : Fin k → ℕ × ℕ, prefixEq k r α γ *
          (branchWeight k w α * branchWeight k w γ *
            U (fun p => (branchMarks k z α p, branchMarks k z γ p)))
  | k, 0, U, hU, w, z => by
    rw [cascadeSqPair_zero, cascadePairSum_cascadeZip k hU]
    simp only [prefixEq_zero, one_mul]
  | 0, r + 1, U, _, w, z => by
    rw [cascadeSqPair_zero_succ]
    simp only [prefixEq_zero_succ, zero_mul, tsum_zero]
  | k + 1, r + 1, U, hU, w, z => by
    have hcons : Measurable (uncurry (fun a : T => fun x : Fin k → T × T =>
        U (Fin.cons (a, a) x))) :=
      hU.comp (measurable_fin_cons.comp
        ((measurable_fst.prodMk measurable_fst).prodMk measurable_snd))
    have hv : Measurable (fun p : T × CascadeSpace T k =>
        cascadeSqPair k r (fun x => U (Fin.cons (p.1, p.1) x)) p.2) :=
      measurable_cascadeSqPair_prod k r hcons
    have hφ : Measurable (fun p : ℝ × (T × CascadeSpace T k) =>
        ENNReal.ofReal p.1 * ENNReal.ofReal p.1 *
          cascadeSqPair k r (fun x => U (Fin.cons (p.2.1, p.2.1) x)) p.2.2) :=
      (measurable_fst.ennreal_ofReal.mul measurable_fst.ennreal_ofReal).mul
        (hv.comp measurable_snd)
    rw [cascadeSqPair_succ, cascadeZip_succ, lintegral_superCounting_superZip _ _ hφ,
      ← tsum_nat_prod_ite (fun n => (w.1 n).2) (fun n j =>
        ENNReal.ofReal ((w.1 n).1 j) * ENNReal.ofReal ((w.1 n).1 j) *
          cascadeSqPair k r (fun x => U (Fin.cons (z.1 n j, z.1 n j) x))
            (cascadeZip k (w.2 n j, z.2 n j))), tsum_fin_succ]
    apply tsum_congr
    intro nj
    have hcol (β : Fin k → ℕ × ℕ) :
        (∑' γ : Fin (k + 1) → ℕ × ℕ,
          prefixEq (k + 1) (r + 1) (Fin.cons nj β) γ *
            (branchWeight (k + 1) w (Fin.cons nj β) * branchWeight (k + 1) w γ *
              U (fun p => (branchMarks (k + 1) z (Fin.cons nj β) p,
                branchMarks (k + 1) z γ p)))) =
        ∑' δ : Fin k → ℕ × ℕ, prefixEq k r β δ *
          (branchWeight (k + 1) w (Fin.cons nj β) * branchWeight (k + 1) w (Fin.cons nj δ) *
            U (fun p => (branchMarks (k + 1) z (Fin.cons nj β) p,
              branchMarks (k + 1) z (Fin.cons nj δ) p))) := by
      rw [tsum_fin_succ]
      simp_rw [prefixEq_succ, mul_assoc, ENNReal.tsum_mul_left, ite_mul, one_mul, zero_mul]
      rw [tsum_ite_eq]
    simp_rw [hcol, branchWeight_succ, branchMarks_succ, pair_fin_cons]
    split_ifs with h
    · rw [cascadeSqPair_cascadeZip k r
        (U := fun x => U (Fin.cons (z.1 nj.1 nj.2, z.1 nj.1 nj.2) x))
        (hU.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))]
      simp_rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro β
      apply tsum_congr
      intro δ
      ring
    · simp

end

end ProbabilityTheory
