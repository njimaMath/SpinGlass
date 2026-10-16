import SpinGlass.Parisi.Variational.ParisiColeHopfSwapZero
import SpinGlass.Parisi.Variational.ParisiSpatialBounds

/-!
# Cole-Hopf rearrangement for actual Parisi suffixes

The comparison includes mass zero and zero variances. Strictness is
derived for the actual finite log-cosh recursion from its positive
curvature, without requiring an ordered intermediate mass list.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- Lemma 14.10.5, (14.383), for nonnegative ordered masses. The
genuine Gaussian expectation handles zero mass, and the identity
operator handles zero variance. -/
theorem coleHopf_swap_le {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m n : ℝ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (v w : ℝ≥0) (x : ℝ) :
    coleHopf m v (coleHopf n w A) x ≤ coleHopf n w (coleHopf m v A) x := by
  rcases eq_or_lt_of_le hn with hn0 | hnpos
  · have hn0' : n = 0 := hn0.symm
    subst n
    rcases eq_or_lt_of_le hnm with hm0 | hmpos
    · have hm0' : m = 0 := hm0.symm
      subst m
      have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
      have hAg := HasLinearGrowth.of_lipschitz hL
      rw [coleHopf_coleHopf hAg hAm, coleHopf_coleHopf hAg hAm, add_comm v w]
    · exact coleHopf_swap_zero_le hAm hA hmpos v w x
  · exact coleHopf_swap_le_of_pos hAm hA hnpos hnm v w x

/-- The strict part (14.384), including inner mass zero, follows
from the concrete Gaussian equality conditions and strict convexity. -/
theorem coleHopf_swap_lt {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) (hconv : StrictConvexOn ℝ univ A)
    {m n : ℝ} (hn : 0 ≤ n) (hnm : n < m) {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0) (x : ℝ) :
    coleHopf m v (coleHopf n w A) x < coleHopf n w (coleHopf m v A) x := by
  rcases eq_or_lt_of_le hn with hn0 | hnpos
  · have hn0' : n = 0 := hn0.symm
    subst n
    exact coleHopf_swap_zero_lt hAm hA hconv hnm hv hw x
  · exact coleHopf_swap_lt_of_pos hAm hA hconv hnpos hnm hv hw x

/-- Every actual finite log-cosh recursion is strictly convex when
its masses lie in the closed physical range. No mass ordering is needed,
so this applies to the intermediate rearranged lists of Section 14.10. -/
theorem coleHopfIterate_logCosh_strictConvex {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hm : ∀ p, ms p ∈ Icc (0 : ℝ) 1) :
    StrictConvexOn ℝ univ (coleHopfIterate j ms vs (parisiLogCoshTerminal 0)) := by
  have hc := (coleHopfIterate_spatial_regular_four ms vs (contDiff_parisiLogCoshTerminal 0 4)
    (exists_bound_iteratedDeriv_parisiLogCoshTerminal_four 0)).1.continuous
  apply strictConvexOn_of_deriv2_pos' convex_univ hc.continuousOn
  intro x _
  have hpos : 0 < Real.exp (-2 * ∑ p, (vs p : ℝ)) / Real.cosh x ^ 2 :=
    div_pos (Real.exp_pos _) (sq_pos_of_ne_zero (Real.cosh_pos x).ne')
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
    hpos.trans_le (coleHopfIterate_logCosh_curvature_lower ms vs hm x)

/-- The strict rearrangement for the actual finite Parisi suffix,
including intermediate lists that are not monotone. -/
theorem coleHopf_swap_logCoshIterate_lt {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hm : ∀ p, ms p ∈ Icc (0 : ℝ) 1) {m n : ℝ} (hn : 0 ≤ n) (hnm : n < m)
    {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0) (x : ℝ) :
    coleHopf m v (coleHopf n w (coleHopfIterate j ms vs (parisiLogCoshTerminal 0))) x <
      coleHopf n w (coleHopf m v (coleHopfIterate j ms vs (parisiLogCoshTerminal 0))) x := by
  have hAm := measurable_coleHopfIterate (L := 1) ms vs
    (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0))
    (fun x y => by simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0 x y)
  have hA : ∀ x y, |coleHopfIterate j ms vs (parisiLogCoshTerminal 0) y -
      coleHopfIterate j ms vs (parisiLogCoshTerminal 0) x| ≤ |y - x| := by
    simpa only [one_mul] using abs_coleHopfIterate_sub_le (L := 1) j ms vs
      (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0))
      (fun x y => by simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0 x y)
  exact coleHopf_swap_lt hAm hA (coleHopfIterate_logCosh_strictConvex ms vs hm) hn hnm hv hw x

end SpinGlass
