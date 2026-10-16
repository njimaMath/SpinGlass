import SpinGlass.Parisi.Coupled.CoupledPairGaussianLayer

/-!
# Finite Gaussian cascades as actual paired Cole-Hopf iterates

Every positive-mass layer is instantiated with its actual independent,
common or antisymmetric Gaussian law. Induction on the finite cascade
proves the complete recursion identity for any separately unit-Lipschitz
terminal. Root expectations at mass zero remain outside this recursion.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

theorem cascadeRec_pairGaussian_comp_add_sum (k : ℕ) :
    ∀ (ps : Fin k → PairColeHopfLevel), (∀ i, 0 < (ps i).mass) →
      ∀ {F : ℝ → ℝ → ℝ}, PairUnitLipschitz F → ∀ x y : ℝ,
    cascadeRec k (fun i => (ps i).mass)
      (siteGaussianMarks (Fin 2) k (fun i => (ps i).variance))
      (fun zs => ENNReal.ofReal (Real.exp
        (F (x + ∑ i, (pairGaussianShift (ps i).kind (zs i)).1)
          (y + ∑ i, (pairGaussianShift (ps i).kind (zs i)).2)))) =
      ENNReal.ofReal (Real.exp (pairColeHopfIterate (List.ofFn ps) F x y)) := by
  induction k with
  | zero =>
    intro ps _ F _ x y
    simp [cascadeRec_zero, pairColeHopfIterate]
  | succ k ih =>
    intro ps hpos F hF x y
    let A := pairColeHopfIterate (List.ofFn (Fin.tail ps)) F
    have hA : PairUnitLipschitz A := pairColeHopfIterate_lipschitz _ hF
    have hns : Fin.tail (fun i => (ps i).mass) = fun i : Fin k => (ps i.succ).mass := rfl
    have hμ : Fin.tail (siteGaussianMarks (Fin 2) (k + 1) (fun i => (ps i).variance)) =
        siteGaussianMarks (Fin 2) k (fun i => (ps i.succ).variance) := by
      funext i
      rfl
    have hinner (z : Fin 2 → ℝ) :
        cascadeRec k (Fin.tail (fun i => (ps i).mass))
          (Fin.tail (siteGaussianMarks (Fin 2) (k + 1) (fun i => (ps i).variance)))
          (fun zs : Fin k → Fin 2 → ℝ => ENNReal.ofReal (Real.exp
            (F (x + ∑ i : Fin (k + 1), (pairGaussianShift (ps i).kind
                ((Fin.cons z zs : Fin (k + 1) → Fin 2 → ℝ) i)).1)
              (y + ∑ i : Fin (k + 1), (pairGaussianShift (ps i).kind
                ((Fin.cons z zs : Fin (k + 1) → Fin 2 → ℝ) i)).2)))) =
          ENNReal.ofReal (Real.exp
            (A (x + (pairGaussianShift (ps 0).kind z).1)
              (y + (pairGaussianShift (ps 0).kind z).2))) := by
      have hh := ih (Fin.tail ps) (fun i => hpos i.succ) hF
        (x + (pairGaussianShift (ps 0).kind z).1)
        (y + (pairGaussianShift (ps 0).kind z).2)
      rw [hns, hμ]
      simpa only [siteGaussianMarks, Fin.tail, Fin.sum_univ_succ, Fin.cons_zero,
        Fin.cons_succ, add_assoc, A] using hh
    rw [cascadeRec_succ]
    simp only [hinner]
    have hpow (z : Fin 2 → ℝ) :
        ENNReal.ofReal (Real.exp (A (x + (pairGaussianShift (ps 0).kind z).1)
            (y + (pairGaussianShift (ps 0).kind z).2))) ^ (ps 0).mass =
          ENNReal.ofReal (Real.exp ((ps 0).mass * A
            (x + (pairGaussianShift (ps 0).kind z).1)
            (y + (pairGaussianShift (ps 0).kind z).2))) := by
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul, mul_comm]
    simp only [hpow]
    change (∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (Real.exp ((ps 0).mass * A
        (x + (pairGaussianShift (ps 0).kind z).1)
        (y + (pairGaussianShift (ps 0).kind z).2)))
        ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 (ps 0).variance)) ^ (1 / (ps 0).mass) = _
    rw [lintegral_exp_mul_pairGaussianShift hA (ps 0) (hpos 0).ne' x y,
      ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    have he : pairColeHopfIterate (List.ofFn ps) F x y = pairColeHopfOperator (ps 0) A x y := by
      rw [List.ofFn_succ]
      rfl
    rw [he]
    congr 2
    field_simp [(hpos 0).ne']

/-- The actual finite positive-mass paired Gaussian Parisi recursion
equals the concrete paired iterate, with no recursion equality assumed. -/
theorem parisiRec_pairGaussian_comp_add_sum {k : ℕ}
    (ps : Fin k → PairColeHopfLevel) (hpos : ∀ i, 0 < (ps i).mass)
    {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) (x y : ℝ) :
    parisiRec k (fun i => (ps i).mass)
      (siteGaussianMarks (Fin 2) k (fun i => (ps i).variance))
      (fun zs => F (x + ∑ i, (pairGaussianShift (ps i).kind (zs i)).1)
        (y + ∑ i, (pairGaussianShift (ps i).kind (zs i)).2)) =
      pairColeHopfIterate (List.ofFn ps) F x y := by
  rw [parisiRec, cascadeRec_pairGaussian_comp_add_sum k ps hpos hF x y,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]

end SpinGlass
