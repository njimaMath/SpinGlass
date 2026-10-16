import SpinGlass.Parisi.Coupled.CoupledSharedColeHopf

/-!
# Common and antisymmetric Gaussian equality conditions

Evenness of the actual log-cosh suffix converts an antisymmetric
mark into a common mark at the reflected second field. This proves
the signed equality condition in (14.381), including unordered suffix
masses in the closed scalar interval.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

noncomputable def signedPairColeHopf (η m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  coleHopf m v (fun z => A (x + z) + A (y + η * z)) 0

@[simp] theorem signedPairColeHopf_one (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (x y : ℝ) :
    signedPairColeHopf 1 m v A x y = sharedPairColeHopf m v A x y := by
  simp only [signedPairColeHopf, sharedPairColeHopf, one_mul]

theorem signedPairColeHopf_neg_one_of_even {A : ℝ → ℝ} (heven : Function.Even A)
    (m : ℝ) (v : ℝ≥0) (x y : ℝ) :
    signedPairColeHopf (-1) m v A x y = sharedPairColeHopf m v A x (-y) := by
  unfold signedPairColeHopf sharedPairColeHopf
  congr 1
  funext z
  rw [show y + (-1) * z = -(-y + z) by ring, heven]

/-- The common/antisymmetric part of (14.374), at its actual
Gaussian law, with the true expectation branch at mass zero. -/
theorem signedPairColeHopf_le {A : ℝ → ℝ} (hAm : Measurable A)
    {L : ℝ} (hA : ∀ x y, |A y - A x| ≤ L * |y - x|) (heven : Function.Even A)
    {η m : ℝ} (hη : η = 1 ∨ η = -1) (hm : 0 ≤ m) (v : ℝ≥0) (x y : ℝ) :
    signedPairColeHopf η m v A x y ≤ coleHopf (2 * m) v A x + coleHopf (2 * m) v A y := by
  rcases hη with rfl | rfl
  · rw [signedPairColeHopf_one]
    exact sharedPairColeHopf_le hAm hA hm v x y
  · rw [signedPairColeHopf_neg_one_of_even heven]
    simpa only [coleHopf_even hAm heven (2 * m) v y] using sharedPairColeHopf_le hAm hA hm v x (-y)

/-- Equality in a positive nondegenerate signed Gaussian layer
forces the previous effective fields to agree with the same sign. -/
theorem signedPairColeHopf_eq_implies_fields_eq {A : ℝ → ℝ} (hAm : Measurable A)
    {L : ℝ} (hA : ∀ x y, |A y - A x| ≤ L * |y - x|) (heven : Function.Even A)
    (hconv : StrictConvexOn ℝ univ A) {η m : ℝ} (hη : η = 1 ∨ η = -1)
    (hm : 0 < m) {v : ℝ≥0} (hv : v ≠ 0) (x y : ℝ)
    (he : signedPairColeHopf η m v A x y = coleHopf (2 * m) v A x + coleHopf (2 * m) v A y) :
    x = η * y := by
  rcases hη with rfl | rfl
  · rw [signedPairColeHopf_one] at he
    simpa only [one_mul] using sharedPairColeHopf_eq_implies_fields_eq hAm hA hconv hm hv x y he
  · rw [signedPairColeHopf_neg_one_of_even heven] at he
    have hy := coleHopf_even hAm heven (2 * m) v y
    rw [← hy] at he
    simpa only [neg_one_mul] using sharedPairColeHopf_eq_implies_fields_eq hAm hA hconv hm hv x (-y) he

theorem signedPairColeHopf_lt_of_fields_ne {A : ℝ → ℝ} (hAm : Measurable A)
    {L : ℝ} (hA : ∀ x y, |A y - A x| ≤ L * |y - x|) (heven : Function.Even A)
    (hconv : StrictConvexOn ℝ univ A) {η m : ℝ} (hη : η = 1 ∨ η = -1)
    (hm : 0 < m) {v : ℝ≥0} (hv : v ≠ 0) {x y : ℝ} (hne : x ≠ η * y) :
    signedPairColeHopf η m v A x y < coleHopf (2 * m) v A x + coleHopf (2 * m) v A y :=
  lt_of_le_of_ne (signedPairColeHopf_le hAm hA heven hη hm.le v x y)
    (fun he => hne (signedPairColeHopf_eq_implies_fields_eq hAm hA heven hconv hη hm hv x y he))

theorem coleHopfIterateList_logCosh_even (l : List (ℝ × ℝ≥0)) :
    Function.Even (coleHopfIterateList l (parisiLogCoshTerminal 0)) := by
  have hL : ∀ x y, |parisiLogCoshTerminal 0 y - parisiLogCoshTerminal 0 x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0
  induction l with
  | nil =>
    intro x
    simp only [coleHopfIterateList_nil, parisiLogCoshTerminal, zero_add, Real.cosh_neg]
  | cons p l ih =>
    exact coleHopf_even
      (lipschitzWith_toNNReal_of_abs_sub_le (abs_coleHopfIterateList_sub_le l hL)).continuous.measurable
      ih p.1 p.2

/-- Book-level signed Gaussian equality for the actual recursive
suffix. Its strict convexity and symmetry are proved, not supplied. -/
theorem signedPairColeHopf_logCoshList_eq_implies_fields_eq (l : List (ℝ × ℝ≥0))
    (hms : ∀ p ∈ l, p.1 ∈ Icc (0 : ℝ) 1) {η m : ℝ} (hη : η = 1 ∨ η = -1)
    (hm : 0 < m) {v : ℝ≥0} (hv : v ≠ 0) (x y : ℝ)
    (he : signedPairColeHopf η m v (coleHopfIterateList l (parisiLogCoshTerminal 0)) x y =
      coleHopf (2 * m) v (coleHopfIterateList l (parisiLogCoshTerminal 0)) x +
        coleHopf (2 * m) v (coleHopfIterateList l (parisiLogCoshTerminal 0)) y) :
    x = η * y := by
  have hL : ∀ x y, |parisiLogCoshTerminal 0 y - parisiLogCoshTerminal 0 x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0
  have hAl := abs_coleHopfIterateList_sub_le l hL
  exact signedPairColeHopf_eq_implies_fields_eq
    (lipschitzWith_toNNReal_of_abs_sub_le hAl).continuous.measurable hAl
    (coleHopfIterateList_logCosh_even l) (coleHopfIterateList_logCosh_strictConvex l hms)
    hη hm hv x y he

theorem signedPairColeHopf_logCoshList_lt_of_fields_ne (l : List (ℝ × ℝ≥0))
    (hms : ∀ p ∈ l, p.1 ∈ Icc (0 : ℝ) 1) {η m : ℝ} (hη : η = 1 ∨ η = -1)
    (hm : 0 < m) {v : ℝ≥0} (hv : v ≠ 0) {x y : ℝ} (hne : x ≠ η * y) :
    signedPairColeHopf η m v (coleHopfIterateList l (parisiLogCoshTerminal 0)) x y <
      coleHopf (2 * m) v (coleHopfIterateList l (parisiLogCoshTerminal 0)) x +
        coleHopf (2 * m) v (coleHopfIterateList l (parisiLogCoshTerminal 0)) y := by
  have hL : ∀ x y, |parisiLogCoshTerminal 0 y - parisiLogCoshTerminal 0 x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0
  have hAl := abs_coleHopfIterateList_sub_le l hL
  exact signedPairColeHopf_lt_of_fields_ne
    (lipschitzWith_toNNReal_of_abs_sub_le hAl).continuous.measurable hAl
    (coleHopfIterateList_logCosh_even l) (coleHopfIterateList_logCosh_strictConvex l hms)
    hη hm hv hne

end SpinGlass
