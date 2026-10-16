import SpinGlass.Parisi.Coupled.CoupledPairColeHopf

/-!
# Finite paired Gaussian comparison and scalar rearrangement

The three concrete Gaussian layer kinds give (14.372)-(14.375).
Their effective scalar masses are doubled exactly at common and
antisymmetric marks. The scalar sorting theorem then applies to the
actual finite list, with genuine expectation levels at mass zero.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

inductive PairColeHopfKind
  | independent
  | common
  | antisymmetric
  deriving DecidableEq

structure PairColeHopfLevel where
  mass : ℝ
  variance : ℝ≥0
  kind : PairColeHopfKind

def PairColeHopfLevel.scalar (p : PairColeHopfLevel) : ℝ × ℝ≥0 :=
  (match p.kind with | .independent => p.mass | _ => 2 * p.mass, p.variance)

noncomputable def pairColeHopfOperator (p : PairColeHopfLevel) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  match p.kind with
  | .independent => independentPairColeHopf p.mass p.variance F
  | .common => correlatedPairColeHopf 1 p.mass p.variance F
  | .antisymmetric => correlatedPairColeHopf (-1) p.mass p.variance F

noncomputable def pairColeHopfIterate : List PairColeHopfLevel → (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ
  | [], F => F
  | p :: l, F => pairColeHopfOperator p (pairColeHopfIterate l F)

def pairColeHopfScalarLevels (l : List PairColeHopfLevel) : List (ℝ × ℝ≥0) := l.map (·.scalar)

theorem PairColeHopfLevel.scalar_mass_nonneg (p : PairColeHopfLevel) (hm : 0 ≤ p.mass) :
    0 ≤ p.scalar.1 := by
  cases hk : p.kind <;> simp only [PairColeHopfLevel.scalar, hk] <;> positivity

theorem pairColeHopfOperator_lipschitz (p : PairColeHopfLevel) {F : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) : PairUnitLipschitz (pairColeHopfOperator p F) := by
  cases hk : p.kind
  · simpa only [pairColeHopfOperator, hk] using independentPairColeHopf_lipschitz hF p.mass p.variance
  · simpa only [pairColeHopfOperator, hk] using correlatedPairColeHopf_lipschitz hF
      (by norm_num : |(1 : ℝ)| = 1) p.mass p.variance
  · simpa only [pairColeHopfOperator, hk] using correlatedPairColeHopf_lipschitz hF
      (by norm_num : |(-1 : ℝ)| = 1) p.mass p.variance

theorem pairColeHopfIterate_lipschitz (l : List PairColeHopfLevel) {F : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) : PairUnitLipschitz (pairColeHopfIterate l F) := by
  induction l with
  | nil => exact hF
  | cons p l ih => exact pairColeHopfOperator_lipschitz p ih

theorem pairColeHopfOperator_mono (p : PairColeHopfLevel) {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) (hFG : ∀ x y, F x y ≤ G x y) (x y : ℝ) :
    pairColeHopfOperator p F x y ≤ pairColeHopfOperator p G x y := by
  cases hk : p.kind
  · simpa only [pairColeHopfOperator, hk] using independentPairColeHopf_mono hF hG hFG p.mass p.variance x y
  · simpa only [pairColeHopfOperator, hk] using correlatedPairColeHopf_mono hF hG hFG
      (by norm_num : |(1 : ℝ)| = 1) p.mass p.variance x y
  · simpa only [pairColeHopfOperator, hk] using correlatedPairColeHopf_mono hF hG hFG
      (by norm_num : |(-1 : ℝ)| = 1) p.mass p.variance x y

theorem pairColeHopfOperator_lt (p : PairColeHopfLevel) {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) (hFG : ∀ x y, F x y < G x y)
    (hm : 0 ≤ p.mass) (x y : ℝ) : pairColeHopfOperator p F x y < pairColeHopfOperator p G x y := by
  cases hk : p.kind
  · simpa only [pairColeHopfOperator, hk] using independentPairColeHopf_lt hF hG hFG hm p.variance x y
  · simpa only [pairColeHopfOperator, hk] using correlatedPairColeHopf_lt hF hG hFG
      (by norm_num : |(1 : ℝ)| = 1) hm p.variance x y
  · simpa only [pairColeHopfOperator, hk] using correlatedPairColeHopf_lt hF hG hFG
      (by norm_num : |(-1 : ℝ)| = 1) hm p.variance x y

theorem pairColeHopfIterate_lt (l : List PairColeHopfLevel) {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) (hFG : ∀ x y, F x y < G x y)
    (hm : ∀ p ∈ l, 0 ≤ p.mass) (x y : ℝ) :
    pairColeHopfIterate l F x y < pairColeHopfIterate l G x y := by
  induction l generalizing x y with
  | nil => exact hFG x y
  | cons p l ih =>
    exact pairColeHopfOperator_lt p (pairColeHopfIterate_lipschitz l hF) (pairColeHopfIterate_lipschitz l hG)
      (ih (fun q hq => hm q (List.mem_cons_of_mem _ hq))) (hm p (List.mem_cons_self)) x y

/-- The actual finite paired recursion is bounded by the sum
of its marginal scalar recursions, equation (14.372). -/
theorem pairColeHopfIterate_logCosh_le_scalar (l : List PairColeHopfLevel)
    (hm : ∀ p ∈ l, 0 ≤ p.mass) (x y : ℝ) :
    pairColeHopfIterate l (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) x y ≤
      coleHopfIterateList (pairColeHopfScalarLevels l) (parisiLogCoshTerminal 0) x +
        coleHopfIterateList (pairColeHopfScalarLevels l) (parisiLogCoshTerminal 0) y := by
  have hL : ∀ x y, |parisiLogCoshTerminal 0 y - parisiLogCoshTerminal 0 x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0
  have hT := pairUnitLipschitz_sum (abs_parisiLogCoshTerminal_sub_le 0)
  induction l generalizing x y with
  | nil => exact le_rfl
  | cons p l ih =>
    let A := coleHopfIterateList (pairColeHopfScalarLevels l) (parisiLogCoshTerminal 0)
    have hAl := abs_coleHopfIterateList_sub_le (pairColeHopfScalarLevels l) hL
    have hAm := (lipschitzWith_toNNReal_of_abs_sub_le hAl).continuous.measurable
    have hAl' : ∀ a b, |A b - A a| ≤ |b - a| := by simpa only [one_mul] using hAl
    have hmono := pairColeHopfOperator_mono p (pairColeHopfIterate_lipschitz l hT)
      (pairUnitLipschitz_sum hAl') (ih (fun q hq => hm q (List.mem_cons_of_mem _ hq))) x y
    apply hmono.trans
    cases hk : p.kind
    · simp only [pairColeHopfOperator, hk, pairColeHopfScalarLevels, List.map_cons,
        PairColeHopfLevel.scalar, coleHopfIterateList_cons]
      exact (independentPairColeHopf_sum hAm hAl p.mass p.variance x y).le
    · simp only [pairColeHopfOperator, hk, pairColeHopfScalarLevels, List.map_cons,
        PairColeHopfLevel.scalar, coleHopfIterateList_cons]
      exact signedPairColeHopf_le hAm hAl (coleHopfIterateList_logCosh_even _)
        (Or.inl rfl) (hm p (List.mem_cons_self)) p.variance x y
    · simp only [pairColeHopfOperator, hk, pairColeHopfScalarLevels, List.map_cons,
        PairColeHopfLevel.scalar, coleHopfIterateList_cons]
      exact signedPairColeHopf_le hAm hAl (coleHopfIterateList_logCosh_even _)
        (Or.inr rfl) (hm p (List.mem_cons_self)) p.variance x y

theorem pairColeHopfScalarLevels_mass_nonneg (l : List PairColeHopfLevel)
    (hm : ∀ p ∈ l, 0 ≤ p.mass) : ∀ p ∈ pairColeHopfScalarLevels l, 0 ≤ p.1 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  exact q.scalar_mass_nonneg (hm q hq)

/-- Combining the actual paired comparison with scalar sorting
gives the finite-list version of (14.375) followed by Lemma 14.10.5. -/
theorem pairColeHopfIterate_logCosh_le_sorted_scalar (l : List PairColeHopfLevel)
    (hm : ∀ p ∈ l, 0 ≤ p.mass) (x y : ℝ) :
    pairColeHopfIterate l (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) x y ≤
      coleHopfIterateList (List.insertionSort parisiLevelMassOrder (pairColeHopfScalarLevels l))
        (parisiLogCoshTerminal 0) x +
      coleHopfIterateList (List.insertionSort parisiLevelMassOrder (pairColeHopfScalarLevels l))
        (parisiLogCoshTerminal 0) y := by
  apply (pairColeHopfIterate_logCosh_le_scalar l hm x y).trans
  exact add_le_add
    (coleHopfIterateList_le_insertionSort (abs_parisiLogCoshTerminal_sub_le 0) _
      (pairColeHopfScalarLevels_mass_nonneg l hm) x)
    (coleHopfIterateList_le_insertionSort (abs_parisiLogCoshTerminal_sub_le 0) _
      (pairColeHopfScalarLevels_mass_nonneg l hm) y)

noncomputable def randomFieldPairColeHopfListValue (μh : Measure ℝ) (l : List PairColeHopfLevel) : ℝ :=
  ∫ h, pairColeHopfIterate l (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) h h ∂μh

theorem integrable_pairColeHopfIterate_externalField {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (l : List PairColeHopfLevel) :
    Integrable (fun h => pairColeHopfIterate l
      (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) h h) μh := by
  let F := fun h => pairColeHopfIterate l
    (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) h h
  have hp := pairColeHopfIterate_lipschitz l (pairUnitLipschitz_sum (abs_parisiLogCoshTerminal_sub_le 0))
  have hF : ∀ x y, |F y - F x| ≤ 2 * |y - x| := fun x y => by
    simpa only [two_mul] using hp x x y y
  apply ((integrable_const |F 0|).add (hμ.abs.const_mul 2)).mono'
    (lipschitzWith_toNNReal_of_abs_sub_le hF).continuous.measurable.aestronglyMeasurable
  refine .of_forall fun h => ?_
  change |F h| ≤ |F 0| + 2 * |h|
  have hh := hF 0 h
  have ha := abs_sub_abs_le_abs_sub (F h) (F 0)
  simp only [sub_zero] at hh
  linarith

theorem randomFieldPairColeHopfListValue_le_scalar {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (l : List PairColeHopfLevel) (hm : ∀ p ∈ l, 0 ≤ p.mass) :
    randomFieldPairColeHopfListValue μh l ≤ 2 * randomFieldColeHopfListValue μh (pairColeHopfScalarLevels l) := by
  have h := integral_mono (integrable_pairColeHopfIterate_externalField hμ l)
    ((integrable_coleHopfIterateList_externalField hμ (pairColeHopfScalarLevels l)).const_mul 2)
    (fun h => by simpa only [two_mul] using pairColeHopfIterate_logCosh_le_scalar l hm h h)
  simpa only [randomFieldPairColeHopfListValue, randomFieldColeHopfListValue, integral_const_mul] using h

theorem randomFieldPairColeHopfListValue_le_sorted_scalar {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (l : List PairColeHopfLevel) (hm : ∀ p ∈ l, 0 ≤ p.mass) :
    randomFieldPairColeHopfListValue μh l ≤
      2 * randomFieldColeHopfListValue μh (List.insertionSort parisiLevelMassOrder (pairColeHopfScalarLevels l)) := by
  apply (randomFieldPairColeHopfListValue_le_scalar hμ l hm).trans
  exact mul_le_mul_of_nonneg_left
    (randomFieldColeHopfListValue_le_insertionSort hμ _ (pairColeHopfScalarLevels_mass_nonneg l hm)) (by norm_num)

/-- Equality in the field-averaged paired and sorted-scalar bound
forces active effective masses to be ordered, the actual scalar
equality conclusion (14.387). -/
theorem parisiActiveLevelMassOrder_of_randomFieldPair_sort_eq
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (l : List PairColeHopfLevel) (hm : ∀ p ∈ l, 0 ≤ p.mass)
    (hscalar : ∀ p ∈ pairColeHopfScalarLevels l, p.1 ∈ Icc (0 : ℝ) 1)
    (he : randomFieldPairColeHopfListValue μh l =
      2 * randomFieldColeHopfListValue μh (List.insertionSort parisiLevelMassOrder (pairColeHopfScalarLevels l))) :
    List.Pairwise parisiActiveLevelMassOrder (pairColeHopfScalarLevels l) := by
  apply parisiActiveLevelMassOrder_of_randomFieldColeHopfList_sort_eq hμ _ hscalar
  have h₁ := randomFieldPairColeHopfListValue_le_scalar hμ l hm
  have h₂ := randomFieldColeHopfListValue_le_insertionSort hμ _ (pairColeHopfScalarLevels_mass_nonneg l hm)
  rw [he] at h₁
  linarith

end SpinGlass
