import SpinGlass.Parisi.Coupled.CoupledInnerFreeMass

/-!
# Physical auxiliary deletion at a free inner mass

The new inner mark has zero auxiliary variance. Deleting it recovers
the original coupled cascade for every nonzero inserted mass, so its
physical pressure has no inserted-mass dependence.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The deterministic inserted auxiliary level erases at any nonzero
free coupled mass, without one-copy mass admissibility. -/
theorem cascadeRec_parisi_inner_free_aux_eq {N k : ℕ} (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (t : ℝ)
    {b : ℝ} (hb : b ≠ 0) (c : (Fin 2 → Config N) → ℝ)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (z₀ : Fin N × Fin 2 → ℝ) :
    cascadeRec (k + 2) (parisiInnerFreeCoupledMasses ms p b)
      (siteGaussianMarks (Fin N × Fin 2) _
        (fun i => parisiInnerAuxSplitVars ξ qs p.castSucc t (parisiSplitIndex p.castSucc i)))
      (pairHamG N _ c H lam a (couplingFactorSgn 1 (p.val + 2) 0)
        (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) z₀) =
      cascadeRec (k + 1) (halveBelow (p.val + 1) (parisiLevelMasses ms))
        (siteGaussianMarks (Fin N × Fin 2) _ (fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i))
        (pairHamG N _ c H lam a (couplingFactorSgn 1 (p.val + 2) 0)
          (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) z₀) := by
  have hmass : parisiInnerFreeCoupledMasses ms p b (parisiInnerFreeMassIndex p) ≠ 0 := by
    rw [parisiInnerFreeCoupledMasses_eq_update, Function.update_self]
    exact hb
  have hdel := cascadeRec_pairHamG_remove_zero_eq (N := N) (k := k + 1) (J := Fin 2)
    (parisiInnerFreeCoupledMasses ms p b)
    (fun i => parisiInnerAuxSplitVars ξ qs p.castSucc t (parisiSplitIndex p.castSucc i))
    (parisiInnerFreeMassIndex p) hmass (parisiInnerAuxSplitVars_zero ξ qs p.castSucc t)
    c H lam a (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) z₀
  have hv := parisiInnerAuxSplitVars_remove_zero ξ qs p.castSucc t
  have hf := parisiSplitFactors_remove_inner p.castSucc
  change (parisiInnerFreeMassIndex p).removeNth
    (fun i => parisiInnerAuxSplitVars ξ qs p.castSucc t (parisiSplitIndex p.castSucc i)) = _ at hv
  change (parisiInnerFreeMassIndex p).removeNth
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) =
      (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) at hf
  rw [parisiInnerFreeCoupledMasses_remove_inner, hv, hf] at hdel
  exact hdel

end SpinGlass
