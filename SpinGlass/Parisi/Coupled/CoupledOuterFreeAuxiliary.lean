import SpinGlass.Parisi.Coupled.CoupledOuterFreeMass

/-!
# Physical auxiliary deletion at a free outer mass

The freely varied shared level has zero auxiliary variance. Its
deletion recovers the original cascade and the left-endpoint replica
prefix at every nonzero scalar mass, including terminal insertions.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

theorem cascadeRec_parisi_outer_free_aux_eq {N k : ℕ} (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t : ℝ)
    {b : ℝ} (hb : b ≠ 0) (c : (Fin 2 → Config N) → ℝ)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (z₀ : Fin N × Fin 2 → ℝ) :
    cascadeRec (k + 2) (parisiOuterFreeCoupledMasses ms p b)
      (siteGaussianMarks (Fin N × Fin 2) _
        (fun i => parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i)))
      (pairHamG N _ c H lam a (couplingFactorSgn 1 (p.val + 2) 0)
        (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) z₀) =
      cascadeRec (k + 1) (halveBelow p.val (parisiLevelMasses ms))
        (siteGaussianMarks (Fin N × Fin 2) _ (fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i))
        (pairHamG N _ c H lam a (couplingFactorSgn 1 (p.val + 1) 0)
          (fun i => couplingFactorSgn 1 (p.val + 1) (i.val + 1)) z₀) := by
  have hmass : parisiOuterFreeCoupledMasses ms p b p.castSucc ≠ 0 := by
    unfold parisiOuterFreeCoupledMasses
    rw [Function.update_self]
    exact div_ne_zero hb (by norm_num)
  have hdel := cascadeRec_pairHamG_remove_zero_eq (N := N) (k := k + 1) (J := Fin 2)
    (parisiOuterFreeCoupledMasses ms p b)
    (fun i => parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i))
    p.castSucc hmass (parisiOuterAuxSplitVars_zero ξ qs p t)
    c H lam a (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) z₀
  rw [parisiOuterFreeCoupledMasses_remove_outer, parisiOuterAuxSplitVars_remove_zero,
    parisiSplitFactors_remove_outer] at hdel
  have hroot : couplingFactorSgn 1 (p.val + 2) 0 = couplingFactorSgn 1 (p.val + 1) 0 := by
    unfold couplingFactorSgn
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  rw [hroot] at hdel
  exact hdel

end SpinGlass
