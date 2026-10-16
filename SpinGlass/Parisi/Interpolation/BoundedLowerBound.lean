import SpinGlass.Parisi.Interpolation.LowerComparison
import SpinGlass.Parisi.Interpolation.TerminalEndpoint
import SpinGlass.Parisi.Minimizer.Full

/-!
# The Parisi lower bound for bounded nondegenerate field laws

Choose a cutoff time using only the profile curvature and target accuracy.
The uniform localization theorem then selects MIN parameters and a single
Gronwall constant before the finite-volume accuracy is chosen.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace SpinGlass

/-- The complete bounded-field case of Talagrand's lower bound. -/
theorem eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy_of_bounded
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hPSD : ∀ N : ℕ, (overlapCovMatrix N ξ).PosSemidef)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ᵐ h ∂μh, |h| ≤ R) :
    ∀ ε > 0, ∀ᶠ N in atTop,
      randomFieldParisiInf μh ξ - ε ≤ iidFieldMixedPSpinFreeEnergy N μh ξ := by
  intro ε hε
  let L := deriv (deriv ξ) 1
  have hL : 0 < L := hξ.second_pos 1 ⟨zero_le_one, le_rfl⟩ one_ne_zero
  let d := min (1 / 2 : ℝ) (ε / (2 * L))
  have hd : 0 < d := lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hL))
  have hdhalf : d ≤ 1 / 2 := min_le_left _ _
  have hdε : L * d ≤ ε / 2 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hL)).1
      (min_le_right (1 / 2 : ℝ) (ε / (2 * L)))
    change d * (2 * L) ≤ ε at hh
    nlinarith only [hh]
  let T := 1 - d
  have hT : T ∈ Ico (0 : ℝ) 1 :=
    ⟨by dsimp only [T]; linarith, by dsimp only [T]; linarith⟩
  obtain ⟨δ, hδ, hlocal⟩ := exists_uniform_parisiGuerraRemainder_bound hμ hξ hPSD hR hbound hT
  obtain ⟨k, ms, qs, hm, hq, hnear, hmin, hfull⟩ :=
    exists_randomFieldParisiMIN hμ.integrable_id hξ hδ
  obtain ⟨C, hC, hCbound⟩ := hlocal k ms qs hm hmin hfull hnear
  let η := ε / (2 * Real.exp (C * T))
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) (Real.exp_pos _))
  have hηeq : η * Real.exp (C * T) = ε / 2 := by
    dsimp only [η]
    field_simp
  filter_upwards [hCbound η hη, eventually_gt_atTop (0 : ℕ)] with N hloc hN
  have hloc' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      parisiGuerraRemainder N μh ξ ms qs t ≤ C *
        (parisiInterpolationBracket μh ξ ms qs t -
          parisiInterpolationPressure N μh ξ ms qs t + η) := by
    have hg := sub_nonneg.2 (parisiInterpolationPressure_le_bracket N k hN hμ.integrable_id
      hξ (hPSD N) ms hm qs hq ⟨ht.1, ht.2.trans hT.2.le⟩)
    simpa only [max_eq_left hg] using hloc t ht
  have hgap := parisiInterpolationGap_le_exp hN hμ.integrable_id hξ (hPSD N) ms hm qs hq
    ⟨hT.1, hT.2.le⟩ hC hη.le hloc' T ⟨hT.1, le_rfl⟩
  rw [hηeq] at hgap
  have htail := parisiInterpolationGap_sub_le_curvature hN hμ.integrable_id hξ (hPSD N)
    ms hm qs hq hT.1 hT.2.le (b := 1) le_rfl
  have hdT : deriv (deriv ξ) 1 * (1 - T) ≤ ε / 2 := by
    simpa only [T, sub_sub_cancel] using hdε
  rw [parisiInterpolationBracket_one μh ξ ms qs hm,
    parisiInterpolationPressure_one hμ.integrable_id ξ ms qs hm.2.1 (hPSD N)] at htail
  have hInf := randomFieldParisiInf_le μh ξ (bddBelow_randomFieldParisiSet_of_talagrand μh hξ)
    hm.1 hm.2.1 hm.2.2 hq.monotone hq.2.1 hq.2.2
  linarith only [htail, hdT, hgap, hInf]

end SpinGlass
