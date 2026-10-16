import SpinGlass.Parisi.Coupled.CoupledCanonicalAuxiliaryTransport
import SpinGlass.Parisi.Coupled.CoupledCanonicalComparison
import SpinGlass.Parisi.Coupled.CoupledOriginalPressure

/-!
# The canonical physical pressure is the original auxiliary pressure

At the physical endpoint, all driven marks have zero coefficients.
Deleting them preserves the exact original auxiliary source order.
Its standard columns are transported to the prescribed Gaussian laws,
and the final mass-one mark has the normalization in (14.312).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The remaining standard auxiliary columns give the actual full
old auxiliary cascade, including its terminal mass-one layer. -/
theorem cascadeRec_parisiCanonical_retained_auxiliary_eq {N k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ)
    (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (z₀ : Fin N × ParisiCanonicalColumns ms r p → ℝ) :
    cascadeRec (k + 1) (halveBelow r.val (parisiLevelMasses ms))
      (siteGaussianMarks (Fin N × ParisiCanonicalColumns ms r p) _ (fun _ => 1))
      (pairHamG N (k + 1) c H lam a
        (parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u)
        (fun i => parisiCanonicalAuxiliaryPieceFactor ξ ms qs negative r p t u
          (.auxiliary i.succ)) z₀) =
    cascadeRec (k + 1) (halveBelow r.val (parisiLevelMasses ms))
      (siteGaussianMarks (Fin N × Fin 2) _
        (fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i))
      (pairHamG N (k + 1) c H lam a (couplingFactorSgn 1 (r.val + 1) 0)
        (fun i => couplingFactorSgn 1 (r.val + 1) (i.val + 1))
        (parisiCanonicalAuxiliaryRootMarksMap ξ ms qs hm r p t z₀)) := by
  let vs : Fin (k + 1) → ℝ≥0 := fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i
  let φ (i : Fin (k + 1)) := canonicalScaledMarksMap (S := Fin N)
    (D := ParisiCanonicalColumns ms r p) (vs i) (fun j => .inr (.inl j))
  let K := fun i : Fin (k + 1) => couplingFactorSgn 1 (r.val + 1) (i.val + 1)
  have hK (i : Fin (k + 1)) :
      parisiCanonicalAuxiliaryPieceFactor ξ ms qs negative r p t u (.auxiliary i.succ) =
        canonicalRightColumn (canonicalPositiveColumn
          (I := Fin (parisiCanonicalRootPieces ms r p).length) (vs i) (K i)) := by
    simp only [parisiCanonicalAuxiliaryPieceFactor, ParisiCanonicalPiece.auxiliaryVariance,
      ParisiCanonicalPiece.isDriven, Bool.false_eq_true, ite_false,
      ParisiCanonicalPiece.variance, parisiAllVars, parisiLevelVars, Fin.val_succ,
      parisiCanonicalAuxiliary_gaussianFactor, vs, K]
  have hmap : (fun i => (siteGaussianMarks (Fin N × ParisiCanonicalColumns ms r p) (k + 1)
      (fun _ => 1) i).map (φ i)) = siteGaussianMarks (Fin N × Fin 2) (k + 1) vs := by
    funext i
    apply map_pi_gaussianReal_canonicalScaledMarksMap
    intro x y h
    exact Sum.inl.inj (Sum.inr.inj h)
  have he : pairHamG N (k + 1) c H lam a
      (parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u)
      (fun i => parisiCanonicalAuxiliaryPieceFactor ξ ms qs negative r p t u
        (.auxiliary i.succ)) z₀ =
      fun zs => pairHamG N (k + 1) c H lam a (couplingFactorSgn 1 (r.val + 1) 0) K
        (parisiCanonicalAuxiliaryRootMarksMap ξ ms qs hm r p t z₀)
        (fun i => φ i (zs i)) := by
    funext zs
    have hmark (l : Fin 2) (s : Fin N) :
        pairBranchMark N (k + 1)
          (parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u)
          (fun i => parisiCanonicalAuxiliaryPieceFactor ξ ms qs negative r p t u
            (.auxiliary i.succ)) z₀ zs l s =
        pairBranchMark N (k + 1) (couplingFactorSgn 1 (r.val + 1) 0) K
          (parisiCanonicalAuxiliaryRootMarksMap ξ ms qs hm r p t z₀)
          (fun i => φ i (zs i)) l s := by
      unfold pairBranchMark
      rw [sum_parisiCanonicalAuxiliaryRootFactor_mul ξ ms qs hm negative r p t u]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      change (∑ j, parisiCanonicalAuxiliaryPieceFactor ξ ms qs negative r p t u
        (.auxiliary i.succ) l j * zs i (s, j)) = ∑ j, K i l j * φ i (zs i) (s, j)
      rw [hK i]
      exact sum_canonicalAuxiliaryPositiveColumn_mul (vs i) (K i) (zs i) l s
    unfold pairHamG pairBranchZX pairBranchHamX
    simp_rw [hmark]
  rw [he, ← cascadeRec_map (k + 1) (halveBelow r.val (parisiLevelMasses ms)) _ φ
    (fun i => measurable_canonicalScaledMarksMap _ _)
    (measurable_pairHamG' N (k + 1) c H lam a (couplingFactorSgn 1 (r.val + 1) 0) K
      (parisiCanonicalAuxiliaryRootMarksMap ξ ms qs hm r p t z₀))]
  simp only [hmap]
  rfl

/-- Every zero-contribution driven layer is removed from the actual
positive canonical cascade, recovering the full old auxiliary law. -/
theorem cascadeRec_parisiCanonical_auxiliary_eq {N k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ)
    (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (z₀ : Fin N × ParisiCanonicalColumns ms r p → ℝ) :
    cascadeRec (parisiCanonicalPositivePieces ms r p).length
      (parisiCanonicalPositiveMasses ms r p)
      (siteGaussianMarks (Fin N × ParisiCanonicalColumns ms r p) _ (fun _ => 1))
      (pairHamG N _ c H lam a (parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u)
        (parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u) z₀) =
    cascadeRec (k + 1) (halveBelow r.val (parisiLevelMasses ms))
      (siteGaussianMarks (Fin N × Fin 2) _
        (fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i))
      (pairHamG N (k + 1) c H lam a (couplingFactorSgn 1 (r.val + 1) 0)
        (fun i => couplingFactorSgn 1 (r.val + 1) (i.val + 1))
        (parisiCanonicalAuxiliaryRootMarksMap ξ ms qs hm r p t z₀)) := by
  have hd := cascadeRec_pairHamG_list_filter_zero
    (Measure.pi (fun _ : Fin N × ParisiCanonicalColumns ms r p => gaussianReal 0 1))
    (ParisiCanonicalPiece.physicalMass ms r p)
    (parisiCanonicalAuxiliaryPieceFactor ξ ms qs negative r p t u)
    ParisiCanonicalPiece.isAuxiliary (parisiCanonicalPositivePieces ms r p)
    (fun e _he ha => parisiCanonicalAuxiliaryPieceFactor_eq_zero ξ ms qs negative r p t u e ha)
    (fun e he _ha => (parisiCanonicalPositivePieces_mass_pos ms hm r p e he).ne')
    c H lam a (parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u) z₀
  rw [parisiCanonicalPositivePieces_filter_auxiliary ms hm r p] at hd
  rw [cascadeRec_pairHamG_ofFn] at hd
  simp only [parisiCanonicalAuxiliary_positive_mass] at hd
  calc
    _ = cascadeRec (k + 1) (halveBelow r.val (parisiLevelMasses ms))
        (siteGaussianMarks (Fin N × ParisiCanonicalColumns ms r p) _ (fun _ => 1))
        (pairHamG N (k + 1) c H lam a
          (parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u)
          (fun i => parisiCanonicalAuxiliaryPieceFactor ξ ms qs negative r p t u
            (.auxiliary i.succ)) z₀) := hd
    _ = _ := cascadeRec_parisiCanonical_retained_auxiliary_eq ξ ms qs hm negative r p t u
      c H lam a z₀

/-- Root and disorder averaging preserve the exact auxiliary cascade
identification. This is a law identity, without field moment restrictions. -/
theorem integral_log_cascadeRec_parisiCanonical_auxiliary_eq {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (Pm : Measure Ω) [IsProbabilityMeasure Pm]
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ)
    (c : (Fin 2 → Config N) → ℝ) (Hf : Ω → EnergySpace N) (hHf : Measurable Hf)
    (lam : ℝ) (a : Fin N × Fin 2 → ℝ) :
    (∫ θ, Real.log (cascadeRec (parisiCanonicalPositivePieces ms r p).length
      (parisiCanonicalPositiveMasses ms r p)
      (siteGaussianMarks (Fin N × ParisiCanonicalColumns ms r p) _ (fun _ => 1))
      (pairHamG N _ c (Hf θ.1) lam a (parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u)
        (parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u) θ.2)).toReal
      ∂Pm.prod (rootMarksLaw N (J := ParisiCanonicalColumns ms r p) 1)) =
    ∫ θ, Real.log (cascadeRec (k + 1) (halveBelow r.val (parisiLevelMasses ms))
      (siteGaussianMarks (Fin N × Fin 2) _
        (fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i))
      (pairHamG N (k + 1) c (Hf θ.1) lam a (couplingFactorSgn 1 (r.val + 1) 0)
        (fun i => couplingFactorSgn 1 (r.val + 1) (i.val + 1)) θ.2)).toReal
      ∂Pm.prod (rootMarksLaw N (J := Fin 2) (parisiAuxRootVar ξ qs t)) := by
  let φ := parisiCanonicalAuxiliaryRootMarksMap (N := N) ξ ms qs hm r p t
  let F := fun θ : Ω × (Fin N × Fin 2 → ℝ) => Real.log
    (cascadeRec (k + 1) (halveBelow r.val (parisiLevelMasses ms))
      (siteGaussianMarks (Fin N × Fin 2) _
        (fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i))
      (pairHamG N (k + 1) c (Hf θ.1) lam a (couplingFactorSgn 1 (r.val + 1) 0)
        (fun i => couplingFactorSgn 1 (r.val + 1) (i.val + 1)) θ.2)).toReal
  have hφ : Measurable φ := measurable_parisiCanonicalAuxiliaryRootMarksMap ξ ms qs hm r p t
  have hFm : Measurable F := (measurable_cascadeRec_prod (k + 1)
    (halveBelow r.val (parisiLevelMasses ms))
    (siteGaussianMarks (Fin N × Fin 2) _
      (fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i))
    (measurable_pairHamG_branchParam N (k + 1) c hHf lam a
      (couplingFactorSgn 1 (r.val + 1) 0)
      (fun i => couplingFactorSgn 1 (r.val + 1) (i.val + 1)))).ennreal_toReal.log
  have hmap : (Pm.prod (rootMarksLaw N (J := ParisiCanonicalColumns ms r p) 1)).map
      (Prod.map id φ) = Pm.prod (rootMarksLaw N (J := Fin 2) (parisiAuxRootVar ξ qs t)) := by
    rw [← Measure.map_prod_map _ _ measurable_id hφ, Measure.map_id]
    exact congrArg (Measure.prod Pm) (map_gaussian_parisiCanonicalAuxiliaryRootMarksMap
      ξ ms qs hm r p t)
  have hi := integral_map (μ := Pm.prod (rootMarksLaw N (J := ParisiCanonicalColumns ms r p) 1))
    (measurable_id.prodMap hφ).aemeasurable hFm.aestronglyMeasurable
  rw [hmap] at hi
  calc
    _ = ∫ θ, F (Prod.map id φ θ)
        ∂Pm.prod (rootMarksLaw N (J := ParisiCanonicalColumns ms r p) 1) := by
      apply integral_congr_ae (.of_forall fun θ => ?_)
      rw [cascadeRec_parisiCanonical_auxiliary_eq ξ ms qs hm negative r p t u]
      rfl
    _ = _ := hi.symm

/-- The physical pressure in the canonical finite-volume comparison
is the original auxiliary pressure plus its terminal normalization (14.312).
All deletion, Gaussian-law and root identifications are proved. -/
theorem parisiCanonicalPressure_eq_original {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    (hN : 0 < N) (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = if negative then -u else u) :
    parisiCanonicalPressure ξ ms qs negative r p t u G₀ a =
      parisiAuxPairPressure ξ ms qs (r.val + 1) t (if negative then -u else u) G₀ a +
        parisiAuxTerminalVar ξ qs t := by
  have hi := integral_log_cascadeRec_parisiCanonical_auxiliary_eq Pm ξ ms qs hm negative r p t u
    (constraintR N (if negative then -u else u)) G₀.U G₀.measU 0 a
  unfold parisiCanonicalPressure coupledG
  simp only [sub_self, Real.sqrt_zero, Real.sqrt_one, zero_smul, one_smul, zero_add]
  rw [hi]
  have hcpos : ∃ σ, 0 < constraintR N (if negative then -u else u) σ :=
    hreach.elim fun σ hσ => ⟨σ, constraintR_pos_of_overlap_eq N hσ⟩
  have hlog (θ : Ω × (Fin N × Fin 2 → ℝ)) :=
    log_cascadeRec_parisi_aux_eq (τ := r.val + 1) ξ ms qs t hm (by omega) (by omega)
      (constraintR_nonneg N _) hcpos (G₀.U θ.1) 0 a θ.2
  have hint := integrable_log_cascadeRec_parisi_aux ξ ms qs (r.val + 1) t
    (if negative then -u else u) hm G₀ a hreach
  unfold parisiAuxPairPressure
  simp only [Nat.add_sub_cancel] at hlog hint ⊢
  simp_rw [hlog]
  rw [integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

end SpinGlass
