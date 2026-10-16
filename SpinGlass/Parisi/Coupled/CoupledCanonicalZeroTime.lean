import SpinGlass.Parisi.Coupled.CoupledCanonicalCouplingComparison
import SpinGlass.Parisi.Coupled.CoupledCanonicalAuxiliaryProjection
import SpinGlass.Parisi.Coupled.CoupledPairGaussianSite
import SpinGlass.Parisi.Coupled.CoupledPairListDeletion
import SpinGlass.Parisi.Coupled.CoupledMainZeroTime

/-!
# The canonical coupling witness at time zero

All driven variances vanish at time zero, including both split pieces.
Deleting these identity operators recovers the actual original auxiliary
site recursion at every coupling. Its proved coupling Taylor gain and
concrete stationary overlap moment give a positive continuous witness
at the zero-time boundary of the compact main-estimate argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

theorem ParisiCanonicalPiece.variance_zero_time_of_not_auxiliary {k : ℕ}
    (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 2)) (v : ℝ)
    (e : ParisiCanonicalPiece k) (he : e.isAuxiliary = false) : e.variance ξ qs p 0 v = 0 := by
  cases e <;> simp [isAuxiliary, variance] at he ⊢

/-- At time zero every driven layer is a zero-variance identity,
including its mass-zero root branch. The exact auxiliary source remains. -/
theorem pairColeHopfIterate_parisiCanonical_zero_time_eq_auxiliary {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) (v : ℝ) (F : ℝ → ℝ → ℝ) :
    pairColeHopfIterate (parisiCanonicalPairLevels ξ ms qs negative r p 0 v) F =
      pairColeHopfIterate ((parisiCanonicalAuxiliaryPieces k).map
        (ParisiCanonicalPiece.toPairLevel ξ ms qs negative r p 0 v)) F := by
  have he := pairColeHopfIterate_map_filter_zero_variance (parisiCanonicalMergedPieces ms r p)
    (ParisiCanonicalPiece.toPairLevel ξ ms qs negative r p 0 v) ParisiCanonicalPiece.isAuxiliary
    (fun e _he ha => e.variance_zero_time_of_not_auxiliary ξ qs p v ha) F
  rw [parisiCanonicalMergedPieces_filter_auxiliary ms hm r p] at he
  exact he

/-- The original two-column auxiliary site value is exactly the
canonical site value at time zero, at every coupling and either sign. -/
theorem parisiCanonicalSiteValue_zero_time_eq_auxiliary {k : ℕ}
    (μh : Measure ℝ) (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (v lam : ℝ) :
    parisiCanonicalSiteValue μh ξ ms qs negative r p 0 v lam =
      randomFieldPairSiteY₀ μh (halveBelow r.val (parisiLevelMasses ms))
        (parisiVar ξ qs 0) (parisiLevelVars ξ qs) lam
        (couplingFactorSgn 1 (r.val + 1) 0)
        (fun i => couplingFactorSgn 1 (r.val + 1) (i.val + 1)) := by
  let q := (ParisiCanonicalPiece.auxiliary 0).toPairLevel ξ ms qs negative r p 0 v
  let ps := fun i : Fin (k + 1) =>
    (ParisiCanonicalPiece.auxiliary i.succ).toPairLevel ξ ms qs negative r p 0 v
  have hq : q.mass = 0 := parisiCanonicalAuxiliaryRoot_mass_zero ms r p
  have hpos : ∀ i, 0 < (ps i).mass := fun i =>
    (ParisiCanonicalPiece.auxiliary i.succ).physicalMass_pos_of_oldLevel_pos ms hm r p
      (by change 0 < i.val + 1; omega)
  have hms : (fun i => (ps i).mass) = halveBelow r.val (parisiLevelMasses ms) := by
    funext i
    exact parisiCanonicalAuxiliary_positive_mass ms r p i
  have hvs : (fun i => (ps i).variance) = parisiLevelVars ξ qs := by
    funext i
    simp [ps, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.variance,
      parisiAllVars, parisiLevelVars]
  have hqv : q.variance = parisiVar ξ qs 0 := by
    simp [q, ParisiCanonicalPiece.toPairLevel, ParisiCanonicalPiece.variance, parisiAllVars]
  have hqK : q.kind.gaussianFactor = couplingFactorSgn 1 (r.val + 1) 0 := by
    change ((ParisiCanonicalPiece.auxiliary 0).kind negative r p).gaussianFactor = _
    rw [← ParisiCanonicalPiece.gaussianFactor_eq_kind, parisiCanonicalAuxiliary_gaussianFactor]
    rfl
  have hK : (fun i => (ps i).kind.gaussianFactor) =
      fun i => couplingFactorSgn 1 (r.val + 1) (i.val + 1) := by
    funext i
    change ((ParisiCanonicalPiece.auxiliary i.succ).kind negative r p).gaussianFactor = _
    rw [← ParisiCanonicalPiece.gaussianFactor_eq_kind, parisiCanonicalAuxiliary_gaussianFactor]
    rfl
  have hl : (parisiCanonicalAuxiliaryPieces k).map
      (ParisiCanonicalPiece.toPairLevel ξ ms qs negative r p 0 v) = q :: List.ofFn ps := by
    simp only [parisiCanonicalAuxiliaryPieces, parisiCanonicalIndices, List.map_ofFn]
    rw [List.ofFn_succ]
    rfl
  unfold parisiCanonicalSiteValue randomFieldPairColeHopfTerminalValue randomFieldPairSiteY₀
  apply integral_congr_ae (.of_forall fun h => ?_)
  rw [pairColeHopfIterate_parisiCanonical_zero_time_eq_auxiliary ξ ms qs hm negative r p v, hl]
  have hh := pairSiteY₀_pairGaussian_eq q hq ps hpos lam (fun _ => h)
  rw [hms, hvs, hqv, hqK, hK] at hh
  exact hh.symm

/-- The original scalar root value is the actual Gaussian-root
average of the full positive log-cosh recursion. -/
theorem integral_logCoshRec_parisiLevels_eq_closedParisiX₀
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) :
    (∫ h, ∫ z, logCoshRec (k + 1) (parisiLevelMasses ms) (parisiLevelVars ξ qs) (h + z)
      ∂gaussianReal 0 (parisiVar ξ qs 0) ∂μh) = ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  have hpos : ∀ i, 0 < parisiLevelMasses ms i := fun i => by
    rw [parisiLevelMasses_apply]
    exact hm.mExt_pos (by omega)
  apply integral_congr_ae (.of_forall fun h => ?_)
  simp_rw [logCoshRec_eq_coleHopfIterate_terminal_zero _ _ hpos]
  rw [closedParisiX₀_translate, coleHopfIterate_succ]
  change _ = coleHopf 0 (parisiVar ξ qs 0) (parisiRootSuffix ξ ms qs) h
  rw [coleHopf_zero]
  rfl

/-- The actual stationary q-moment is the zero-time scalar coupling
slope under the independent field and root-Gaussian law. -/
theorem integral_cascadeTiltTanhSq_parisiLevels_eq_q
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) (r : Fin (k + 1)) :
    (∫ h, ∫ z, cascadeTiltTanhSq (parisiLevelMasses ms) (parisiLevelVars ξ qs) r.val (h + z)
      ∂gaussianReal 0 (parisiVar ξ qs 0) ∂μh) = qs r := by
  have hpos : ∀ i, 0 < parisiLevelMasses ms i := fun i => by
    rw [parisiLevelMasses_apply]
    exact hm.mExt_pos (by omega)
  have hle : ∀ i, parisiLevelMasses ms i ≤ 1 := fun i => by
    rw [parisiLevelMasses_apply]
    exact mExt_le_one (fun j => (hm.2.2 j).le) _
  rw [integral_cascadeTiltTanhSq_externalField_prod _ _ hpos hle r.val (by omega),
    integral_cascadeTiltTanhSq_parisi_eq_outer_initial μh ξ ms qs hm r,
    parisiLeftUSpatialMoment_one_zero_eq_randomFieldParisiQMoment hξ ms qs r hm hmin.1,
    ← (randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin ms qs hm hξ hμ hmin).2 r]

/-- The canonical coupling witness at time zero gains exactly the
quadratic separation from the original stationary overlap, at every
split and either sign. This is the scalar witness for Proposition 14.8.7. -/
theorem parisiCanonicalCouplingGap_zero_time_ge_quadratic
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (v : ℝ) :
    ((if negative then -v else v) - qs r) ^ 2 / 2 ≤
      parisiCanonicalCouplingGap μh ξ ms qs negative r p 0 v
        ((if negative then -v else v) - qs r) := by
  have hmono : Monotone (parisiLevelMasses ms) := fun i j hij => by
    simp only [parisiLevelMasses_apply]
    exact hm.monotone_mExt (by change i.val + 1 ≤ j.val + 1; omega)
  have hpos : ∀ i, 0 < parisiLevelMasses ms i := fun i => by
    rw [parisiLevelMasses_apply]
    exact hm.mExt_pos (by omega)
  have hle : ∀ i, parisiLevelMasses ms i ≤ 1 := fun i => by
    rw [parisiLevelMasses_apply]
    exact mExt_le_one (fun j => (hm.2.2 j).le) _
  have hg := randomFieldPairSiteY₀_coupling_zero_le_gain hμ.integrable_id (parisiLevelMasses ms)
    hmono hpos hle (parisiVar ξ qs 0) (parisiLevelVars ξ qs) (τ := r.val + 1) (by omega)
    (if negative then -v else v)
  dsimp only at hg
  simp only [Nat.add_sub_cancel] at hg
  rw [integral_cascadeTiltTanhSq_parisiLevels_eq_q hμ hξ ms qs hm hmin r,
    integral_logCoshRec_parisiLevels_eq_closedParisiX₀ μh ξ ms qs hm] at hg
  unfold parisiCanonicalCouplingGap
  rw [parisiCanonicalSiteValue_zero_time_eq_auxiliary μh ξ ms qs hm negative r p v]
  have hneg : -(qs r - (if negative then -v else v)) = (if negative then -v else v) - qs r := by
    ring
  rw [hneg] at hg
  nlinarith

end SpinGlass
