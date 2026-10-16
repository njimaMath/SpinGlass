import SpinGlass.Parisi.Field.FieldLawContinuity
import SpinGlass.Parisi.Field.FieldMoments
import SpinGlass.Parisi.Analytic.FieldTruncation

/-!
# Removing boundedness of the external-field law

The actual finite-volume pressure and Parisi infimum are uniformly close
to their bounded-field approximations. Positive clipping preserves the
nondegeneracy hypothesis. Consequently a lower bound proved for bounded
nondegenerate site laws implies the original finite-second-moment claim.
The bounded-law lower bound remains an explicit hypothesis of this reduction.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace SpinGlass

/-- Symmetric clipping is applied to the scalar site law before taking
independent product coordinates for the spin system. -/
noncomputable def truncatedExternalFieldLaw (μh : Measure ℝ) (R : ℝ) : Measure ℝ :=
  μh.map (Aristotle.clip R)

instance isProbabilityMeasure_truncatedExternalFieldLaw (μh : Measure ℝ)
    [IsProbabilityMeasure μh] (R : ℝ) :
    IsProbabilityMeasure (truncatedExternalFieldLaw μh R) :=
  Measure.isProbabilityMeasure_map (Aristotle.continuous_clip R).aemeasurable

/-- The approximating law has the claimed bounded support, including
atoms created at either endpoint by clipping. -/
theorem ae_abs_le_truncatedExternalFieldLaw (μh : Measure ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ h ∂truncatedExternalFieldLaw μh R, |h| ≤ R := by
  apply (ae_map_iff (Aristotle.continuous_clip R).aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)).2
  exact .of_forall fun h => (Aristotle.clip_bounds hR h).1

/-- Every nonnegative clipping has a finite first moment. -/
theorem integrable_clip_externalField (μh : Measure ℝ) [IsProbabilityMeasure μh]
    {R : ℝ} (hR : 0 ≤ R) : Integrable (Aristotle.clip R) μh := by
  apply Integrable.of_bound (Aristotle.continuous_clip R).aestronglyMeasurable R
  exact .of_forall fun h => by
    simpa only [Real.norm_eq_abs] using (Aristotle.clip_bounds hR h).1

/-- A positive cutoff preserves both the finite second moment and its
strict positivity; no atom-free assumption is needed. -/
theorem NondegenerateExternalFieldLaw.truncated {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh)
    {R : ℝ} (hR : 0 < R) :
    NondegenerateExternalFieldLaw (truncatedExternalFieldLaw μh R) := by
  obtain ⟨_, hint, hpos⟩ :=
    Aristotle.clipped_law_nondegenerate hμ.sq_integrable hμ.second_moment_pos hR
  exact ⟨hint, hpos⟩

/-- The clipping error for the actual quenched pressure is independent
of the volume. The transformed field remains i.i.d. across sites. -/
theorem abs_iidFieldMixedPSpinFreeEnergy_sub_truncated_le {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμ : Integrable id μh) {R : ℝ} (hR : 0 ≤ R)
    {N : ℕ} (hN : 0 < N) (ξ : ℝ → ℝ) (hPSD : (overlapCovMatrix N ξ).PosSemidef) :
    |iidFieldMixedPSpinFreeEnergy N μh ξ -
      iidFieldMixedPSpinFreeEnergy N (truncatedExternalFieldLaw μh R) ξ| ≤
        ∫ h, |h - Aristotle.clip R h| ∂μh := by
  simpa only [Measure.map_id, id_eq, truncatedExternalFieldLaw] using
    abs_iidFieldMixedPSpinFreeEnergy_map_sub_le measurable_id
      (Aristotle.continuous_clip R).measurable hμ (integrable_clip_externalField μh hR)
      hN ξ hPSD

/-- Taking the variational infimum retains the same clipping error,
uniformly over all admissible level counts and parameter arrays. -/
theorem abs_randomFieldParisiInf_sub_truncated_le {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμ : Integrable id μh) {R : ℝ} (hR : 0 ≤ R)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) :
    |randomFieldParisiInf μh ξ - randomFieldParisiInf (truncatedExternalFieldLaw μh R) ξ| ≤
      ∫ h, |h - Aristotle.clip R h| ∂μh := by
  simpa only [Measure.map_id, id_eq, truncatedExternalFieldLaw] using
    abs_randomFieldParisiInf_map_sub_le measurable_id
      (Aristotle.continuous_clip R).measurable hμ (integrable_clip_externalField μh hR) hξ

/-- Choose one positive cutoff before the volume. Both errors are
smaller than the prescribed accuracy with no dependence on volume. -/
theorem exists_truncatedExternalFieldLaw_uniform_approximation {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hPSD : ∀ N : ℕ, (overlapCovMatrix N ξ).PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧
      |randomFieldParisiInf μh ξ - randomFieldParisiInf (truncatedExternalFieldLaw μh R) ξ| < ε ∧
      ∀ N : ℕ, 0 < N →
        |iidFieldMixedPSpinFreeEnergy N μh ξ -
          iidFieldMixedPSpinFreeEnergy N (truncatedExternalFieldLaw μh R) ξ| < ε := by
  have he := (Aristotle.tendsto_integral_clip_error hμ).eventually (gt_mem_nhds hε)
  obtain ⟨R, hR, herror⟩ := ((eventually_gt_atTop (0 : ℝ)).and he).exists
  exact ⟨R, hR, (abs_randomFieldParisiInf_sub_truncated_le hμ hR.le hξ).trans_lt herror,
    fun N hN => (abs_iidFieldMixedPSpinFreeEnergy_sub_truncated_le hμ hR.le hN ξ
      (hPSD N)).trans_lt herror⟩

/-- Conditional approximation reduction: eventual lower bounds for
every positive clipping imply the lower bound for the original site law.
The chosen cutoff is fixed before taking the volume sufficiently large. -/
theorem eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy_of_truncations
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hPSD : ∀ N : ℕ, (overlapCovMatrix N ξ).PosSemidef)
    (htrunc : ∀ R : ℝ, 0 < R → ∀ ε > 0, ∀ᶠ N in atTop,
      randomFieldParisiInf (truncatedExternalFieldLaw μh R) ξ - ε ≤
        iidFieldMixedPSpinFreeEnergy N (truncatedExternalFieldLaw μh R) ξ) :
    ∀ ε > 0, ∀ᶠ N in atTop,
      randomFieldParisiInf μh ξ - ε ≤ iidFieldMixedPSpinFreeEnergy N μh ξ := by
  intro ε hε
  obtain ⟨R, hR, hP, hp⟩ := exists_truncatedExternalFieldLaw_uniform_approximation
    hμ hξ hPSD (show 0 < ε / 3 by positivity)
  filter_upwards [htrunc R hR (ε / 3) (by positivity), eventually_gt_atTop (0 : ℕ)]
    with N hbound hN
  have hvalue := (abs_lt.1 hP).2
  have hpressure := (abs_lt.1 (hp N hN)).1
  linarith

/-- The finite-second-moment capstone reduces to bounded
nondegenerate probability site laws under exactly the same profile and
Hamiltonian assumptions. This theorem does not assume concentration of
the original unbounded field and does not prove the bounded-law case. -/
theorem eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy_of_bounded_laws
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hPSD : ∀ N : ℕ, (overlapCovMatrix N ξ).PosSemidef)
    (hbounded : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      NondegenerateExternalFieldLaw ν → (∃ R : ℝ, 0 < R ∧ ∀ᵐ h ∂ν, |h| ≤ R) →
        ∀ ε > 0, ∀ᶠ N in atTop,
          randomFieldParisiInf ν ξ - ε ≤ iidFieldMixedPSpinFreeEnergy N ν ξ) :
    ∀ ε > 0, ∀ᶠ N in atTop,
      randomFieldParisiInf μh ξ - ε ≤ iidFieldMixedPSpinFreeEnergy N μh ξ := by
  apply eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy_of_truncations
    hμ.integrable_id hξ hPSD
  intro R hR
  exact hbounded (truncatedExternalFieldLaw μh R) (hμ.truncated hR)
    ⟨R, hR, ae_abs_le_truncatedExternalFieldLaw μh hR.le⟩

end SpinGlass
