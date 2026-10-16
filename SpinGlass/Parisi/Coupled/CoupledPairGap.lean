import SpinGlass.Parisi.Coupled.CoupledPairRecursion
import SpinGlass.Parisi.Coupled.CoupledPairEquality

/-!
# Strict gaps from incompatible independent and shared marks

A positive nondegenerate shared or antisymmetric layer has a strict
scalar comparison at some pair of fields. Earlier independent Gaussian
marks with nonzero variance make that gap strict at every pair of fields.
This proves the independent-mark exclusion needed in (14.382), allowing
arbitrary intervening layers and genuine mass-zero expectations.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

@[simp] theorem pairColeHopfOperator_zero_variance (p : PairColeHopfLevel)
    (hv : p.variance = 0) (F : ℝ → ℝ → ℝ) (x y : ℝ) :
    pairColeHopfOperator p F x y = F x y := by
  cases hk : p.kind <;>
    simp only [pairColeHopfOperator, hk, independentPairColeHopf, correlatedPairColeHopf,
      hv, coleHopf_zero_var, add_zero, mul_zero]

theorem pairColeHopfOperator_sum_le (p : PairColeHopfLevel) {A : ℝ → ℝ}
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) (heven : Function.Even A)
    (hm : 0 ≤ p.mass) (x y : ℝ) :
    pairColeHopfOperator p (fun a b => A a + A b) x y ≤
      coleHopf p.scalar.1 p.variance A x + coleHopf p.scalar.1 p.variance A y := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hAm := (lipschitzWith_toNNReal_of_abs_sub_le hL).continuous.measurable
  cases hk : p.kind
  · simp only [pairColeHopfOperator, PairColeHopfLevel.scalar, hk]
    exact (independentPairColeHopf_sum hAm hL p.mass p.variance x y).le
  · simp only [pairColeHopfOperator, PairColeHopfLevel.scalar, hk]
    exact signedPairColeHopf_le hAm hL heven (Or.inl rfl) hm p.variance x y
  · simp only [pairColeHopfOperator, PairColeHopfLevel.scalar, hk]
    exact signedPairColeHopf_le hAm hL heven (Or.inr rfl) hm p.variance x y

theorem pairColeHopfOperator_preserves_exists_lt (p : PairColeHopfLevel) {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) (hFG : ∀ x y, F x y ≤ G x y)
    (hstrict : ∃ x y, F x y < G x y) (hm : 0 ≤ p.mass) :
    ∃ x y, pairColeHopfOperator p F x y < pairColeHopfOperator p G x y := by
  obtain ⟨x, y, hxy⟩ := hstrict
  by_cases hv : p.variance = 0
  · exact ⟨x, y, by simpa only [pairColeHopfOperator_zero_variance p hv] using hxy⟩
  · refine ⟨x, y, ?_⟩
    cases hk : p.kind
    · simpa only [pairColeHopfOperator, hk] using independentPairColeHopf_lt_of_exists_lt hF hG hFG
        ⟨x, y, hxy⟩ hm hv x y
    · simpa only [pairColeHopfOperator, hk] using correlatedPairColeHopf_lt_of_exists_diagonal_lt hF hG hFG
        (by norm_num : |(1 : ℝ)| = 1) hm hv x y
        ⟨0, by simpa only [add_zero, mul_zero] using hxy⟩
    · simpa only [pairColeHopfOperator, hk] using correlatedPairColeHopf_lt_of_exists_diagonal_lt hF hG hFG
        (by norm_num : |(-1 : ℝ)| = 1) hm hv x y
        ⟨0, by simpa only [add_zero, mul_zero] using hxy⟩

theorem pairColeHopfIterate_head_correlated_exists_gap (p : PairColeHopfLevel) (l : List PairColeHopfLevel)
    (hm : ∀ q ∈ l, 0 ≤ q.mass) (hscalar : ∀ q ∈ pairColeHopfScalarLevels l, q.1 ∈ Icc (0 : ℝ) 1)
    (hkind : p.kind ≠ .independent) (hpos : 0 < p.mass) (hv : p.variance ≠ 0) :
    ∃ x y, pairColeHopfIterate (p :: l)
      (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) x y <
      coleHopfIterateList (pairColeHopfScalarLevels (p :: l)) (parisiLogCoshTerminal 0) x +
        coleHopfIterateList (pairColeHopfScalarLevels (p :: l)) (parisiLogCoshTerminal 0) y := by
  let A := coleHopfIterateList (pairColeHopfScalarLevels l) (parisiLogCoshTerminal 0)
  have hL : ∀ x y, |parisiLogCoshTerminal 0 y - parisiLogCoshTerminal 0 x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0
  have hAl := abs_coleHopfIterateList_sub_le (pairColeHopfScalarLevels l) hL
  have hAl' : ∀ x y, |A y - A x| ≤ |y - x| := by simpa only [one_mul] using hAl
  have hmono := pairColeHopfOperator_mono p
    (pairColeHopfIterate_lipschitz l (pairUnitLipschitz_sum (abs_parisiLogCoshTerminal_sub_le 0)))
    (pairUnitLipschitz_sum hAl') (pairColeHopfIterate_logCosh_le_scalar l hm) 0 1
  refine ⟨0, 1, hmono.trans_lt ?_⟩
  cases hk : p.kind
  · exact (hkind hk).elim
  · simp only [pairColeHopfOperator, hk, pairColeHopfScalarLevels, List.map_cons,
      PairColeHopfLevel.scalar, coleHopfIterateList_cons]
    exact signedPairColeHopf_logCoshList_lt_of_fields_ne _ hscalar (Or.inl rfl) hpos hv (by norm_num)
  · simp only [pairColeHopfOperator, hk, pairColeHopfScalarLevels, List.map_cons,
      PairColeHopfLevel.scalar, coleHopfIterateList_cons]
    exact signedPairColeHopf_logCoshList_lt_of_fields_ne _ hscalar (Or.inr rfl) hpos hv (by norm_num)

/-- Any positive nondegenerate correlated mark yields a strict
comparison at some pair of fields. All earlier layer kinds are allowed. -/
theorem pairColeHopfIterate_exists_gap_of_correlated (l : List PairColeHopfLevel)
    (hm : ∀ p ∈ l, 0 ≤ p.mass) (hscalar : ∀ p ∈ pairColeHopfScalarLevels l, p.1 ∈ Icc (0 : ℝ) 1)
    (hcor : ∃ p ∈ l, p.kind ≠ .independent ∧ 0 < p.mass ∧ p.variance ≠ 0) :
    ∃ x y, pairColeHopfIterate l (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) x y <
      coleHopfIterateList (pairColeHopfScalarLevels l) (parisiLogCoshTerminal 0) x +
        coleHopfIterateList (pairColeHopfScalarLevels l) (parisiLogCoshTerminal 0) y := by
  have hL : ∀ x y, |parisiLogCoshTerminal 0 y - parisiLogCoshTerminal 0 x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0
  induction l with
  | nil => simp at hcor
  | cons p l ih =>
    have hml : ∀ q ∈ l, 0 ≤ q.mass := fun q hq => hm q (List.mem_cons_of_mem _ hq)
    have hsl : ∀ q ∈ pairColeHopfScalarLevels l, q.1 ∈ Icc (0 : ℝ) 1 := fun q hq =>
      hscalar q (by simpa only [pairColeHopfScalarLevels, List.map_cons] using List.mem_cons_of_mem p.scalar hq)
    obtain ⟨q, hq, hkind, hpos, hv⟩ := hcor
    rcases List.mem_cons.1 hq with heq | hq
    · subst q
      exact pairColeHopfIterate_head_correlated_exists_gap p l hml hsl hkind hpos hv
    · let A := coleHopfIterateList (pairColeHopfScalarLevels l) (parisiLogCoshTerminal 0)
      have hAl := abs_coleHopfIterateList_sub_le (pairColeHopfScalarLevels l) hL
      have hAl' : ∀ x y, |A y - A x| ≤ |y - x| := by simpa only [one_mul] using hAl
      obtain ⟨x, y, hxy⟩ := pairColeHopfOperator_preserves_exists_lt p
        (pairColeHopfIterate_lipschitz l (pairUnitLipschitz_sum (abs_parisiLogCoshTerminal_sub_le 0)))
        (pairUnitLipschitz_sum hAl') (pairColeHopfIterate_logCosh_le_scalar l hml)
        (ih hml hsl ⟨q, hq, hkind, hpos, hv⟩) (hm p (List.mem_cons_self))
      refine ⟨x, y, hxy.trans_le ?_⟩
      exact pairColeHopfOperator_sum_le p hAl' (coleHopfIterateList_logCosh_even _) (hm p (List.mem_cons_self)) x y

/-- A strict gap at every pair of effective fields survives
every preceding nonnegative physical layer, including mass zero. -/
theorem pairColeHopfIterate_prefix_lt_scalar (pre tail : List PairColeHopfLevel)
    (hm : ∀ p ∈ pre, 0 ≤ p.mass)
    (hgap : ∀ x y, pairColeHopfIterate tail
      (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) x y <
      coleHopfIterateList (pairColeHopfScalarLevels tail) (parisiLogCoshTerminal 0) x +
        coleHopfIterateList (pairColeHopfScalarLevels tail) (parisiLogCoshTerminal 0) y) (x y : ℝ) :
    pairColeHopfIterate (pre ++ tail)
      (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) x y <
      coleHopfIterateList (pairColeHopfScalarLevels (pre ++ tail)) (parisiLogCoshTerminal 0) x +
        coleHopfIterateList (pairColeHopfScalarLevels (pre ++ tail)) (parisiLogCoshTerminal 0) y := by
  have hL : ∀ x y, |parisiLogCoshTerminal 0 y - parisiLogCoshTerminal 0 x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0
  induction pre generalizing x y with
  | nil => exact hgap x y
  | cons p pre ih =>
    let A := coleHopfIterateList (pairColeHopfScalarLevels (pre ++ tail)) (parisiLogCoshTerminal 0)
    have hAl := abs_coleHopfIterateList_sub_le (pairColeHopfScalarLevels (pre ++ tail)) hL
    have hAl' : ∀ x y, |A y - A x| ≤ |y - x| := by simpa only [one_mul] using hAl
    have hs := pairColeHopfOperator_lt p
      (pairColeHopfIterate_lipschitz (pre ++ tail) (pairUnitLipschitz_sum (abs_parisiLogCoshTerminal_sub_le 0)))
      (pairUnitLipschitz_sum hAl') (ih (fun q hq => hm q (List.mem_cons_of_mem _ hq)))
      (hm p (List.mem_cons_self)) x y
    exact hs.trans_le (pairColeHopfOperator_sum_le p hAl' (coleHopfIterateList_logCosh_even _)
      (hm p (List.mem_cons_self)) x y)

/-- The independent-mark part of (14.382): a nonzero independent
layer before any positive nonzero correlated layer forces a strict
finite-recursion gap at every pair of fields. -/
theorem pairColeHopfIterate_lt_scalar_of_independent_before_correlated
    (pre tail : List PairColeHopfLevel) (q : PairColeHopfLevel)
    (hpre : ∀ p ∈ pre, 0 ≤ p.mass) (hq : 0 ≤ q.mass) (hqkind : q.kind = .independent)
    (hqv : q.variance ≠ 0) (htail : ∀ p ∈ tail, 0 ≤ p.mass)
    (hscalar : ∀ p ∈ pairColeHopfScalarLevels tail, p.1 ∈ Icc (0 : ℝ) 1)
    (hcor : ∃ p ∈ tail, p.kind ≠ .independent ∧ 0 < p.mass ∧ p.variance ≠ 0) (x y : ℝ) :
    pairColeHopfIterate (pre ++ q :: tail)
      (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) x y <
      coleHopfIterateList (pairColeHopfScalarLevels (pre ++ q :: tail)) (parisiLogCoshTerminal 0) x +
        coleHopfIterateList (pairColeHopfScalarLevels (pre ++ q :: tail)) (parisiLogCoshTerminal 0) y := by
  have hL : ∀ x y, |parisiLogCoshTerminal 0 y - parisiLogCoshTerminal 0 x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0
  let A := coleHopfIterateList (pairColeHopfScalarLevels tail) (parisiLogCoshTerminal 0)
  have hAl := abs_coleHopfIterateList_sub_le (pairColeHopfScalarLevels tail) hL
  have hAl' : ∀ x y, |A y - A x| ≤ |y - x| := by simpa only [one_mul] using hAl
  apply pairColeHopfIterate_prefix_lt_scalar pre (q :: tail) hpre (fun a b => ?_) x y
  have hs := independentPairColeHopf_lt_of_exists_lt
    (pairColeHopfIterate_lipschitz tail (pairUnitLipschitz_sum (abs_parisiLogCoshTerminal_sub_le 0)))
    (pairUnitLipschitz_sum hAl') (pairColeHopfIterate_logCosh_le_scalar tail htail)
    (pairColeHopfIterate_exists_gap_of_correlated tail htail hscalar hcor) hq hqv a b
  have hbound := pairColeHopfOperator_sum_le q hAl' (coleHopfIterateList_logCosh_even _) hq a b
  simp only [pairColeHopfOperator, hqkind] at hbound
  simpa only [pairColeHopfIterate, pairColeHopfOperator, hqkind, pairColeHopfScalarLevels,
    List.map_cons, PairColeHopfLevel.scalar, coleHopfIterateList_cons, A] using hs.trans_le hbound

theorem randomFieldPairColeHopfListValue_lt_scalar_of_independent_before_correlated
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (pre tail : List PairColeHopfLevel) (q : PairColeHopfLevel)
    (hpre : ∀ p ∈ pre, 0 ≤ p.mass) (hq : 0 ≤ q.mass) (hqkind : q.kind = .independent)
    (hqv : q.variance ≠ 0) (htail : ∀ p ∈ tail, 0 ≤ p.mass)
    (hscalar : ∀ p ∈ pairColeHopfScalarLevels tail, p.1 ∈ Icc (0 : ℝ) 1)
    (hcor : ∃ p ∈ tail, p.kind ≠ .independent ∧ 0 < p.mass ∧ p.variance ≠ 0) :
    randomFieldPairColeHopfListValue μh (pre ++ q :: tail) <
      2 * randomFieldColeHopfListValue μh (pairColeHopfScalarLevels (pre ++ q :: tail)) := by
  let l := pre ++ q :: tail
  have hF := integrable_pairColeHopfIterate_externalField hμ l
  have hG := (integrable_coleHopfIterateList_externalField hμ (pairColeHopfScalarLevels l)).const_mul 2
  have hs (h : ℝ) : pairColeHopfIterate l
      (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) h h <
        2 * coleHopfIterateList (pairColeHopfScalarLevels l) (parisiLogCoshTerminal 0) h := by
    simpa only [two_mul] using pairColeHopfIterate_lt_scalar_of_independent_before_correlated
      pre tail q hpre hq hqkind hqv htail hscalar hcor h h
  have hn : (∫ h, pairColeHopfIterate l
      (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) h h ∂μh) <
      ∫ h, 2 * coleHopfIterateList (pairColeHopfScalarLevels l) (parisiLogCoshTerminal 0) h ∂μh := by
    apply lt_of_le_of_ne (integral_mono hF hG fun h => (hs h).le)
    intro he
    have hae := (integral_eq_iff_of_ae_le hF hG (.of_forall fun h => (hs h).le)).1 he
    obtain ⟨h, hh⟩ := hae.exists
    exact (hs h).ne hh
  simpa only [randomFieldPairColeHopfListValue, randomFieldColeHopfListValue, integral_const_mul] using hn

end SpinGlass
