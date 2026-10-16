import SpinGlass.Parisi.Concentration.PairTiltPressureGap

/-!
# Concentration for bounded site laws

For a bounded-support site law, clipping fixes every field coordinate
almost surely. Thus the concentration and pressure-gap estimates apply
directly to the original shared field and its actual product law.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N k : ℕ} {J : Type*} [Fintype J]

/-- Coordinate clipping fixes an i.i.d. field with bounded site law,
also in a product with arbitrary independent probability data. -/
theorem ae_clip_field_eq_of_bounded_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μh : Measure ℝ) [IsProbabilityMeasure μh] {R : ℝ}
    (hbound : ∀ᵐ h ∂μh, |h| ≤ R) :
    ∀ᵐ z : Ω × (Fin N → ℝ) ∂P.prod (externalFieldVecLaw N μh),
      (fun i => Aristotle.clip R (z.2 i)) = z.2 := by
  have ha : ∀ᵐ a ∂externalFieldVecLaw N μh, ∀ i, |a i| ≤ R := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (fun _ : Fin N => μh) i).quasiMeasurePreserving.ae hbound
  filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae ha] with z hz
  exact funext fun i => Aristotle.clip_eq_self (hz i)

/-- The tilted logarithm with the original i.i.d. field shared by the
two replicas. Its definition does not include any truncation. -/
noncomputable def pairHamRandomFieldLogTiltMass (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    (c : (Fin 2 → Config N) → ℝ) (lam : ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z : (EnergySpace N × (Fin N × J → ℝ)) × (Fin N → ℝ)) : ℝ :=
  pairHamLogTiltMass ms vs c z.1.1 lam (sharedReplicaSiteField z.2) K₀ K z.1.2

/-- The unnormalized cascade log pressure with the original shared field. -/
noncomputable def pairHamRandomFieldLogPressure (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    (c : (Fin 2 → Config N) → ℝ) (lam : ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z : (EnergySpace N × (Fin N × J → ℝ)) × (Fin N → ℝ)) : ℝ :=
  Real.log (cascadeRec k ms (siteGaussianMarks (Fin N × J) k vs)
    (pairHamG N k c z.1.1 lam (sharedReplicaSiteField z.2) K₀ K z.1.2)).toReal

/-- The full Gaussian and field variance bound under a bounded original
site law. Integrability follows from the same concrete hypotheses. -/
theorem integrable_and_hasSubgaussianMGF_pairHamRandomFieldLogTiltMass
    (μh : Measure ℝ) [IsProbabilityMeasure μh]
    {S : Matrix (Config N) (Config N) ℝ} (hS : S.PosSemidef)
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (v₀ : ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (lam : ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    {D d R : ℝ} (hD : 0 ≤ D) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hbound : ∀ᵐ h ∂μh, |h| ≤ R)
    (hdiag : ∀ σ, S σ σ ≤ (N : ℝ) * D) (hK : ∀ l, ∑ j, K₀ l j ^ 2 ≤ d) :
    let P := ((multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)).prod
      (externalFieldVecLaw N μh)
    let F := pairHamRandomFieldLogTiltMass ms vs c lam K₀ K
    Integrable F P ∧ HasSubgaussianMGF (fun z => F z - ∫ w, F w ∂P)
      ((N : ℝ) * (32 * (D + (v₀ : ℝ) * d) + 16 * R ^ 2)).toNNReal P := by
  let P := ((multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)).prod
    (externalFieldVecLaw N μh)
  have he : pairHamClippedLogTiltMass ms vs c lam K₀ K R =ᵐ[P]
      pairHamRandomFieldLogTiltMass ms vs c lam K₀ K := by
    filter_upwards [ae_clip_field_eq_of_bounded_law
      ((multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)) μh hbound] with z hz
    simp only [pairHamClippedLogTiltMass, pairHamRandomFieldLogTiltMass, hz]
  obtain ⟨hi, hh⟩ := integrable_and_hasSubgaussianMGF_pairHamClippedLogTiltMass μh hS
    ms vs v₀ hc0 hc1 hcpos hsm hpos hlt lam K₀ K hD hd hR hdiag hK
  refine ⟨hi.congr he, hh.congr ?_⟩
  exact he.sub (.of_forall fun _ => integral_congr_ae he)

/-- The pressure-gap estimate for the original field law, with explicit
exponential decay uniform over every parameter satisfying the same bounds. -/
theorem integral_pairHamConstrainedTiltMass_bounded_field_le_of_pressure_gap
    (hN : 0 < N) (μh : Measure ℝ) [IsProbabilityMeasure μh]
    {S : Matrix (Config N) (Config N) ℝ} (hS : S.PosSemidef)
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (v₀ : ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (lam : ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    {D d R : ℝ} (hD : 0 ≤ D) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hbound : ∀ᵐ h ∂μh, |h| ≤ R)
    (hdiag : ∀ σ, S σ σ ≤ (N : ℝ) * D) (hK : ∀ l, ∑ j, K₀ l j ^ 2 ≤ d)
    {b ε : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hblower : ∀ i, b ≤ ms i) (hε : 0 < ε) :
    let P := ((multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)).prod
      (externalFieldVecLaw N μh)
    let C := 1 + 32 * (D + (v₀ : ℝ) * d) + 16 * R ^ 2
    (∫ z, (pairHamRandomFieldLogPressure ms vs c lam K₀ K z -
      pairHamRandomFieldLogPressure ms vs (fun _ => 1) lam K₀ K z) ∂P) ≤ -ε * N →
    (∫ z, (pairHamConstrainedTiltMass ms vs c z.1.1 lam
      (sharedReplicaSiteField z.2) K₀ K z.1.2).toReal ∂P) ≤
      Real.exp (-(b * ε) * N / 2) + Real.exp (-((b * ε) ^ 2 * N) / (8 * C)) := by
  dsimp only
  intro hgap
  have he := ae_clip_field_eq_of_bounded_law (N := N)
    ((multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)) μh hbound
  have hpressure (c : (Fin 2 → Config N) → ℝ) :
      pairHamClippedLogPressure ms vs c lam K₀ K R =ᵐ[
        ((multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)).prod
          (externalFieldVecLaw N μh)] pairHamRandomFieldLogPressure ms vs c lam K₀ K := by
    filter_upwards [he] with z hz
    simp only [pairHamClippedLogPressure, pairHamRandomFieldLogPressure, hz]
  have hgap' : (∫ z, (pairHamClippedLogPressure ms vs c lam K₀ K R z -
      pairHamClippedLogPressure ms vs (fun _ => 1) lam K₀ K R z)
      ∂((multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)).prod
        (externalFieldVecLaw N μh)) ≤ -ε * N := by
    calc
      _ = ∫ z, (pairHamRandomFieldLogPressure ms vs c lam K₀ K z -
          pairHamRandomFieldLogPressure ms vs (fun _ => 1) lam K₀ K z)
          ∂((multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)).prod
            (externalFieldVecLaw N μh) := by
        apply integral_congr_ae
        filter_upwards [hpressure c, hpressure (fun _ => 1)] with z hc hu
        rw [hc, hu]
      _ ≤ -ε * N := hgap
  have hh := integral_pairHamConstrainedTiltMass_clipped_le_of_pressure_gap hN μh hS ms vs v₀
    hc0 hc1 hcpos hsm hpos hlt lam K₀ K hD hd hR hdiag hK hb hb1 hblower hε hgap'
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [he] with z hz
  rw [hz]

end SpinGlass
