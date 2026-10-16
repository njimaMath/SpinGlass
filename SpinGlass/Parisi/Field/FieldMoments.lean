import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# External-field moment assumptions

The field law and its moment consequences are independent of the Parisi
overlap calculus. Probability-measure assumptions remain explicit at each use.
-/

open MeasureTheory

namespace SpinGlass

/-- A finite second moment under a finite site law supplies its first moment. -/
lemma integrable_externalField_of_integrable_sq
    {μh : Measure ℝ} [IsFiniteMeasure μh]
    (hμh : Integrable (fun h : ℝ => h ^ 2) μh) : Integrable id μh :=
  ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hμh).integrable
    (by norm_num)

/-- Talagrand's nondegeneracy condition for the external-field law, in the form
`$0 < \mathbb E h^2 < \infty$`. -/
structure NondegenerateExternalFieldLaw (μh : Measure ℝ) : Prop where
  sq_integrable : Integrable (fun h : ℝ => h ^ 2) μh
  second_moment_pos : 0 < ∫ h, h ^ 2 ∂μh

/-- A finite second moment under a probability law supplies the first-moment integrability
needed for the Parisi functional. -/
lemma NondegenerateExternalFieldLaw.integrable_id
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh) :
    Integrable id μh :=
  integrable_externalField_of_integrable_sq hμ.sq_integrable

/-- A constant external field is nondegenerate exactly when it is nonzero. -/
@[simp] theorem nondegenerateExternalFieldLaw_dirac_iff (h : ℝ) :
    NondegenerateExternalFieldLaw (Measure.dirac h) ↔ h ≠ 0 := by
  constructor
  · intro hμ
    simpa only [integral_dirac, sq_pos_iff] using hμ.second_moment_pos
  · intro hh
    exact ⟨integrable_dirac (by simp), by simpa using sq_pos_of_ne_zero hh⟩

end SpinGlass
