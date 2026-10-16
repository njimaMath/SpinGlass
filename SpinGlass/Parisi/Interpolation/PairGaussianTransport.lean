import SpinGlass.Parisi.Interpolation.CascadeMarkTransport
import SpinGlass.Parisi.Interpolation.PairHamiltonian
import SpinGlass.Parisi.Interpolation.PressureLaw
import SpinGlass.Parisi.Concentration.PairBranchMeeting

/-!
# The Gaussian law of the interpolating constrained meeting mass

Transport of the full independent mark array identifies the original
square-root interpolation with the physical time-scaled Gaussian law.
The identity remains valid at zero variance and at both time endpoints.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

theorem cascadePairObservable_pairHamGt_scaling (r : ℕ) (t : ℝ)
    (c : (Fin 2 → Config N) → ℝ) (h : Fin N → ℝ) (H : EnergySpace N) (z : Fin N → ℝ)
    (w : CascadeWeights k) (y : CascadeMarks (Fin N → ℝ) k) :
    cascadePairObservable k r
      (unscaledPairHamG N k c (Real.sqrt t • H) h (fun i => Real.sqrt (1 - t) * z i))
      (unscaledHamG N k (Real.sqrt t • H) h (fun i => Real.sqrt (1 - t) * z i)) w
      (cascadeMarksMap k (fun _ x i => Real.sqrt (1 - t) * x i) y) =
        cascadePairObservable k r (pairHamGt N k t c h H z) (hamG N k t h H z) w y := by
  rw [cascadePairObservable_cascadeMarksMap k r _ (fun _ => by fun_prop)
    (measurable_unscaledPairHamG _ _ _ _) (measurable_unscaledHamG _ _ _)]
  have hU : (fun x => unscaledPairHamG N k c (Real.sqrt t • H) h
      (fun i => Real.sqrt (1 - t) * z i)
      (fun p => ((fun i => Real.sqrt (1 - t) * (x p).1 i),
        (fun i => Real.sqrt (1 - t) * (x p).2 i)))) = pairHamGt N k t c h H z :=
    funext fun x => (pairHamGt_eq_unscaled N k t c h H z x).symm
  have hG : (fun x => unscaledHamG N k (Real.sqrt t • H) h
      (fun i => Real.sqrt (1 - t) * z i) (fun p i => Real.sqrt (1 - t) * x p i)) =
        hamG N k t h H z := funext fun x => unscaledHamG_interpolation_eq_hamG t H h z x
  rw [hU, hG]

/-- The actual constrained tree expectation under the fixed positive-level
law is the physical branch-meeting mass under its scaled Gaussian law. -/
theorem integral_pairHamGt_meeting_eq_unscaledBranchMeetingMass
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (r : ℕ) {t : ℝ} (ht : t ≤ 1)
    (c : (Fin 2 → Config N) → ℝ) (h : Fin N → ℝ) (H : EnergySpace N) (z : Fin N → ℝ) :
    (∫ q : CascadeWeights k × CascadeMarks (Fin N → ℝ) k,
      cascadePairObservable k r (pairHamGt N k t c h H z) (hamG N k t h H z) q.1 q.2 -
        cascadePairObservable k (r + 1) (pairHamGt N k t c h H z) (hamG N k t h H z) q.1 q.2
      ∂(cascadeWeightsLaw k ms).prod (cascadeMarksLaw k (gaussianMarks N k vs))) =
      unscaledBranchMeetingMass ms (fun p => (1 - t).toNNReal * vs p) r c
        (Real.sqrt t • H) h (fun i => Real.sqrt (1 - t) * z i) := by
  let f := fun _ : Fin k => fun x : Fin N → ℝ => fun i => Real.sqrt (1 - t) * x i
  have hf (p) : MeasurePreserving (f p) (gaussianMarks N k vs p)
      (gaussianMarks N k (fun p => (1 - t).toNNReal * vs p) p) :=
    ⟨by unfold f; fun_prop, map_pi_gaussianReal_sqrt_scale _ (sub_nonneg.2 ht)⟩
  let H' := Real.sqrt t • H
  let z' := fun i => Real.sqrt (1 - t) * z i
  let F := fun ω : CascadeSpace (Fin N → ℝ) k =>
    (unscaledBranchPrefixMass N k r c H' h z' ω).toReal -
      (unscaledBranchPrefixMass N k (r + 1) c H' h z' ω).toReal
  have hF : Measurable F :=
    (measurable_unscaledBranchPrefixMass r c H' h z').ennreal_toReal.sub
      (measurable_unscaledBranchPrefixMass (r + 1) c H' h z').ennreal_toReal
  have hzip : Measurable (fun q : CascadeWeights k × CascadeMarks (Fin N → ℝ) k =>
      F (cascadeZip k q)) := hF.comp (measurable_cascadeZip k)
  have hT := (MeasurePreserving.id (cascadeWeightsLaw k ms)).prod
    (measurePreserving_cascadeMarksMap k (gaussianMarks N k vs)
      (gaussianMarks N k (fun p => (1 - t).toNNReal * vs p)) f hf)
  unfold unscaledBranchMeetingMass
  change _ = ∫ ω, F ω ∂cascadeLaw k ms
    (gaussianMarks N k (fun p => (1 - t).toNNReal * vs p))
  rw [cascadeLaw_eq_map_cascadeZip,
    integral_map (measurable_cascadeZip k).aemeasurable hF.aestronglyMeasurable,
    ← hT.map_eq, integral_map hT.measurable.aemeasurable hzip.aestronglyMeasurable]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  change _ = cascadePairObservable k r (unscaledPairHamG N k c H' h z')
    (unscaledHamG N k H' h z') q.1 (cascadeMarksMap k f q.2) -
      cascadePairObservable k (r + 1) (unscaledPairHamG N k c H' h z')
        (unscaledHamG N k H' h z') q.1 (cascadeMarksMap k f q.2)
  rw [cascadePairObservable_pairHamGt_scaling N k, cascadePairObservable_pairHamGt_scaling N k]

end

end SpinGlass
