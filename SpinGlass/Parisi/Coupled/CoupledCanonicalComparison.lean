import SpinGlass.Parisi.Coupled.CoupledCanonicalGaussianColumns
import SpinGlass.Parisi.Coupled.CoupledRootSignedVariance

/-!
# Finite-volume comparison for the actual canonical merge

The compressed path, positive suffix and product-Gaussian root columns
instantiate the coupled comparison theorem. All covariance, tangent,
support, mass and correction inputs are proved from the original parameters.
Identification of this pressure with the original auxiliary pressure and
of its site recursion with the paired finite list are separate bridges.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable def parisiCanonicalPressure {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∫ θ, Real.log
    (cascadeRec (parisiCanonicalPositivePieces ms r p).length
      (parisiCanonicalPositiveMasses ms r p)
      (siteGaussianMarks (Fin N × ParisiCanonicalColumns ms r p) _ (fun _ => 1))
      (coupledG N (if negative then -u else u) a
        (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u)
        (parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u)
        (parisiCanonicalDrivenFactor ξ ms qs negative r p t u)
        (parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u)
        (parisiTimeProfile ξ t) G₀ 1 θ)).toReal
    ∂Pm.prod (rootMarksLaw N (J := ParisiCanonicalColumns ms r p) 1)

/-- The concrete canonical finite-volume bound for every realizable
signed overlap in the chosen split interval. In particular, no Gaussian
covariance identity or physical-pressure bound is assumed. -/
theorem parisiCanonicalPressure_le_siteValue {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = if negative then -u else u) :
    parisiCanonicalPressure ξ ms qs negative r p t u G₀ a ≤
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ j, pairSiteY₀
        (parisiCanonicalPositiveMasses ms r p) 1 (fun _ => 1) lam (fun l => a (j, l))
        (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u +
          parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u)
        (fun i => parisiCanonicalDrivenFactor ξ ms qs negative r p t u i +
          parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u i) -
        lam * (if negative then -u else u) - t * parisiCorrection ξ ms qs := by
  have hpos := parisiCanonicalPositiveMasses_pos ms hm r p
  have hle := parisiCanonicalPositiveMasses_le_one ms hm r p
  have hmono := parisiCanonicalPositiveMasses_monotone ms r p
  have hb := coupled_bound'_of_monotone N hN (parisiTimeProfile ξ t)
    (parisiCanonicalCompressedRho ms qs negative r p u) (if negative then -u else u)
    (parisiCanonicalCompressedRho_zero ms qs negative r p u)
    (S := Icc (-1 : ℝ) 1) (parisiCanonicalCompressedRho_mem_Icc ms qs hq negative r p hu)
    (fun x _ q hq' => parisiTimeProfile_tangent_line_le_signed hξ ht.1 hq' x)
    (deriv_parisiTimeProfile_zero hξ t) G₀ 1 (fun _ => 1)
    (J₁ := canonicalDrivenColumns (ParisiCanonicalColumnHalf ms r p))
    (L₀ := parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u)
    (L₀' := parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u)
    (L := parisiCanonicalDrivenFactor ξ ms qs negative r p t u)
    (L' := parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u)
    (fun l l' => by
      simpa only [NNReal.coe_one, one_mul] using
        gram_parisiCanonicalDrivenRootFactor hξ ms qs hm hq negative r p ht.1 hu l l')
    (fun i l l' => by
      simpa only [NNReal.coe_one, one_mul] using
        gram_parisiCanonicalDrivenFactor hξ ms qs hm hq negative r p ht.1 hu i l l')
    (fun l j hj => canonicalLeftColumn_zero_of_not_mem _ l j hj)
    (fun i l j hj => canonicalLeftColumn_zero_of_not_mem _ l j hj)
    (fun l j hj => canonicalRightColumn_zero_of_mem _ l j hj)
    (fun i l j hj => canonicalRightColumn_zero_of_mem _ l j hj)
    a lam (parisiCanonicalPositiveMasses ms r p) hmono hpos hle hreach
  rw [integral_parisiRec_pairCoshF_siteField N _ hpos hle,
    coupledLevelSum_parisiCanonical_compressed_eq_correction hξ ms qs hm hq negative r p t hu] at hb
  have hu1 : u ≤ 1 := hu.2.trans (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 (p.val + 1)).2
  rw [pairDiagDefect_parisiCanonicalCompressedRho_terminal _ ms qs negative r p hu1, add_zero] at hb
  exact hb

end SpinGlass
