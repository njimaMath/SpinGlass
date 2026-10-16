import SpinGlass.Parisi.Concentration.PairTiltBranchIdentity
import SpinGlass.Parisi.Concentration.CascadePairBounds

/-!
# Real-valued joint branch-meeting masses

The averaged difference of successive normalized prefix sums equals
the original constrained tilt times the mass increment. Both prefix
averages are integrable, so this is an identity of ordinary expectations.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N k : ℕ}

/-- The normalized constrained Gibbs numerator for branches sharing
their first `r` positive levels. -/
noncomputable def unscaledBranchPrefixMass (N k r : ℕ)
    (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (h z : Fin N → ℝ)
    (ω : CascadeSpace (Fin N → ℝ) k) : ℝ≥0∞ :=
  cascadeSqPair k r (unscaledPairHamG N k c H h z) ω *
    (cascadeSum k (unscaledHamG N k H h z) ω)⁻¹ ^ 2

/-- The joint constrained mass at meeting level `r`, averaged over the
tree while keeping interaction disorder, site field and root marks fixed. -/
noncomputable def unscaledBranchMeetingMass (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    (r : ℕ) (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (h z : Fin N → ℝ) : ℝ :=
  ∫ ω, (unscaledBranchPrefixMass N k r c H h z ω).toReal -
    (unscaledBranchPrefixMass N k (r + 1) c H h z ω).toReal
    ∂cascadeLaw k ms (gaussianMarks N k vs)

theorem measurable_unscaledBranchPrefixMass (r : ℕ)
    (c : (Fin 2 → Config N) → ℝ) (H : EnergySpace N) (h z : Fin N → ℝ) :
    Measurable (unscaledBranchPrefixMass N k r c H h z) :=
  (measurable_cascadeSqPair k r (measurable_unscaledPairHamG c H h z)).mul
    ((measurable_cascadeSum k (measurable_unscaledHamG H h z)).inv.pow_const 2)

theorem unscaledBranchPrefixMass_le_one (r : ℕ)
    {c : (Fin 2 → Config N) → ℝ} (hc1 : ∀ σ, c σ ≤ 1)
    (H : EnergySpace N) (h z : Fin N → ℝ) (ω : CascadeSpace (Fin N → ℝ) k) :
    unscaledBranchPrefixMass N k r c H h z ω ≤ 1 := by
  apply cascadeSqPair_mul_inv_sq_le_one k r (measurable_unscaledHamG H h z) _ ω
  intro x
  rw [← unscaledPairHamG_one_eq_prod]
  unfold unscaledPairHamG
  exact ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun σ _ =>
    mul_le_mul_of_nonneg_right (hc1 σ) (Real.exp_nonneg _))

theorem lintegral_unscaledBranchPrefixMass_ne_top
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (r : ℕ)
    {c : (Fin 2 → Config N) → ℝ} (hc1 : ∀ σ, c σ ≤ 1)
    (H : EnergySpace N) (h z : Fin N → ℝ) :
    (∫⁻ ω, unscaledBranchPrefixMass N k r c H h z ω
      ∂cascadeLaw k ms (gaussianMarks N k vs)) ≠ ∞ := by
  apply ne_top_of_le_ne_top (show (1 : ℝ≥0∞) ≠ ∞ from ENNReal.one_ne_top)
  calc
    _ ≤ ∫⁻ _ω, (1 : ℝ≥0∞) ∂cascadeLaw k ms (gaussianMarks N k vs) :=
      lintegral_mono (unscaledBranchPrefixMass_le_one r hc1 H h z)
    _ = 1 := by simp

theorem integrable_unscaledBranchPrefixMass
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (r : ℕ)
    {c : (Fin 2 → Config N) → ℝ} (hc1 : ∀ σ, c σ ≤ 1)
    (H : EnergySpace N) (h z : Fin N → ℝ) :
    Integrable (fun ω => (unscaledBranchPrefixMass N k r c H h z ω).toReal)
      (cascadeLaw k ms (gaussianMarks N k vs)) :=
  integrable_toReal_of_lintegral_ne_top
    (measurable_unscaledBranchPrefixMass r c H h z).aemeasurable
    (lintegral_unscaledBranchPrefixMass_ne_top ms vs r hc1 H h z)

/-- The actual joint tree mass equals the original Gaussian tilted mass
multiplied by the mass increment, including the first and last levels. -/
theorem unscaledBranchMeetingMass_eq_tilt
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) {c : (Fin 2 → Config N) → ℝ} (hc1 : ∀ σ, c σ ≤ 1)
    (H : EnergySpace N) (h : Fin N → ℝ) (z : Fin N × Fin 2 → ℝ) :
    unscaledBranchMeetingMass ms vs r.val c H h (fun i => z (i, 0)) =
      (mExt ms (r.val + 1) - mExt ms r.val) *
        (pairHamConstrainedTiltMass (halveBelow r.val ms) vs c H 0 (sharedReplicaSiteField h)
          (couplingFactorSgn 1 (r.val + 1) 0)
          (fun p => couplingFactorSgn 1 (r.val + 1) (p.val + 1)) z).toReal := by
  let P := cascadeLaw k ms (gaussianMarks N k vs)
  let F := fun j => unscaledBranchPrefixMass N k j c H h (fun i => z (i, 0))
  have hfin (j) : (∫⁻ ω, F j ω ∂P) ≠ ∞ :=
    lintegral_unscaledBranchPrefixMass_ne_top ms vs j hc1 H h _
  have hi (j) : Integrable (fun ω => (F j ω).toReal) P :=
    integrable_unscaledBranchPrefixMass ms vs j hc1 H h _
  have he (j) : (∫ ω, (F j ω).toReal ∂P) = (∫⁻ ω, F j ω ∂P).toReal :=
    integral_toReal (measurable_unscaledBranchPrefixMass j c H h _).aemeasurable
      (.of_forall fun ω => (unscaledBranchPrefixMass_le_one j hc1 H h _ ω).trans_lt
        ENNReal.one_lt_top)
  have htiltfin : pairHamConstrainedTiltMass (halveBelow r.val ms) vs c H 0
      (sharedReplicaSiteField h) (couplingFactorSgn 1 (r.val + 1) 0)
      (fun p => couplingFactorSgn 1 (r.val + 1) (p.val + 1)) z ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (pairHamConstrainedTiltMass_le_one _ _ hc1
      (halveBelow_pos hm.2.1 _) (halveBelow_le_one (fun i => (hm.2.2 i).le) _) H 0 _ _ _ z)
  have hh := congrArg ENNReal.toReal (lintegral_unscaledPairHamG_succ_add_tilt
    ms vs hm r c H h z)
  change ((∫⁻ ω, F (r.val + 1) ω ∂P) + _).toReal = (∫⁻ ω, F r.val ω ∂P).toReal at hh
  rw [ENNReal.toReal_add (hfin _) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htiltfin),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (hm.mExt_gap_pos r).le] at hh
  change (∫ ω, (F r.val ω).toReal - (F (r.val + 1) ω).toReal ∂P) = _
  rw [integral_sub (hi _) (hi _), he, he]
  linarith only [hh]

/-- Joint measurability of the original tilted mass in the interaction,
root marks and shared site field. Empty constraints are allowed. -/
theorem measurable_pairHamConstrainedTiltMass_original (ms : Fin k → ℝ)
    (vs : Fin k → ℝ≥0) (r : ℕ) (c : (Fin 2 → Config N) → ℝ) :
    Measurable (fun z : (EnergySpace N × (Fin N × Fin 2 → ℝ)) × (Fin N → ℝ) =>
      pairHamConstrainedTiltMass (halveBelow r ms) vs c z.1.1 0 (sharedReplicaSiteField z.2)
        (couplingFactorSgn 1 (r + 1) 0)
        (fun p => couplingFactorSgn 1 (r + 1) (p.val + 1)) z.1.2) := by
  unfold pairHamConstrainedTiltMass
  apply measurable_cascadeTilt_prod
  · unfold Function.uncurry pairHamG pairBranchZX pairBranchHamX pairBranchMark
      sharedReplicaSiteField
    fun_prop
  · unfold Function.uncurry pairHamG pairBranchZX pairBranchHamX pairBranchMark
      sharedReplicaSiteField
    fun_prop

theorem measurable_unscaledBranchMeetingMass
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) {c : (Fin 2 → Config N) → ℝ} (hc1 : ∀ σ, c σ ≤ 1) :
    Measurable (fun z : (EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ) =>
      unscaledBranchMeetingMass ms vs r.val c z.1.1 z.2 z.1.2) := by
  let E := fun z : (EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ) =>
    ((z.1.1, fun ij : Fin N × Fin 2 => z.1.2 ij.1), z.2)
  have hE : Measurable E := by unfold E; fun_prop
  have hh := (measurable_pairHamConstrainedTiltMass_original ms vs r.val c).comp hE
  have he : (fun z : (EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ) =>
      unscaledBranchMeetingMass ms vs r.val c z.1.1 z.2 z.1.2) =
      fun z => (mExt ms (r.val + 1) - mExt ms r.val) *
        (pairHamConstrainedTiltMass (halveBelow r.val ms) vs c (E z).1.1 0
          (sharedReplicaSiteField (E z).2) (couplingFactorSgn 1 (r.val + 1) 0)
          (fun p => couplingFactorSgn 1 (r.val + 1) (p.val + 1)) (E z).1.2).toReal := by
    funext z
    exact unscaledBranchMeetingMass_eq_tilt ms vs hm r hc1 z.1.1 z.2 (E z).1.2
  rw [he]
  exact measurable_const.mul hh.ennreal_toReal

end SpinGlass
