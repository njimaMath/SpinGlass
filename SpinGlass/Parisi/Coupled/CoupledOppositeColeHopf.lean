import SpinGlass.Parisi.Coupled.CoupledPairGap

/-!
# Opposite Gaussian directions give full paired support

Two nonzero common/antisymmetric Gaussian marks span the two effective
fields. Equality of an ordered recursive comparison therefore forces
terminal equality everywhere. This supplies the signed-root contradiction
in the equality analysis of (14.380)-(14.382).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

theorem correlatedPairColeHopf_opposite_eq_implies_eq {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) (hFG : ∀ x y, F x y ≤ G x y)
    {η : ℝ} (hη : η = 1 ∨ η = -1) {m n : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n)
    {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0) (x y : ℝ)
    (he : correlatedPairColeHopf η m v (correlatedPairColeHopf (-η) n w F) x y =
      correlatedPairColeHopf η m v (correlatedPairColeHopf (-η) n w G) x y) : F = G := by
  have hηabs : |η| = 1 := by rcases hη with rfl | rfl <;> norm_num
  have hηneg : |-η| = 1 := by rw [abs_neg, hηabs]
  have hηsq : η ^ 2 = 1 := by rcases hη with rfl | rfl <;> norm_num
  have hinner := correlatedPairColeHopf_mono hF hG hFG hηneg n w
  have hout := correlatedPairColeHopf_eq_implies_diagonal_eq
    (correlatedPairColeHopf_lipschitz hF hηneg n w)
    (correlatedPairColeHopf_lipschitz hG hηneg n w) hinner hηabs hm hv x y he
  funext a b
  let z := ((a - x) + η * (b - y)) / 2
  let r := ((a - x) - η * (b - y)) / 2
  have hin := correlatedPairColeHopf_eq_implies_diagonal_eq hF hG hFG hηneg hn hw
    (x + z) (y + η * z) (hout z) r
  have hx : x + z + r = a := by dsimp [z, r]; ring
  have hy : y + η * z + -η * r = b := by
    calc
      y + η * z + -η * r = y + η ^ 2 * (b - y) := by dsimp [z, r]; ring
      _ = b := by rw [hηsq]; ring
  simpa only [hx, hy] using hin

theorem correlatedPairColeHopf_opposite_lt_of_exists_lt {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) (hFG : ∀ x y, F x y ≤ G x y)
    (hstrict : ∃ x y, F x y < G x y) {η : ℝ} (hη : η = 1 ∨ η = -1)
    {m n : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0) (x y : ℝ) :
    correlatedPairColeHopf η m v (correlatedPairColeHopf (-η) n w F) x y <
      correlatedPairColeHopf η m v (correlatedPairColeHopf (-η) n w G) x y := by
  have hηabs : |η| = 1 := by rcases hη with rfl | rfl <;> norm_num
  have hηneg : |-η| = 1 := by rw [abs_neg, hηabs]
  have hle := correlatedPairColeHopf_mono
    (correlatedPairColeHopf_lipschitz hF hηneg n w)
    (correlatedPairColeHopf_lipschitz hG hηneg n w)
    (correlatedPairColeHopf_mono hF hG hFG hηneg n w) hηabs m v x y
  apply lt_of_le_of_ne hle
  intro he
  have hall := correlatedPairColeHopf_opposite_eq_implies_eq hF hG hFG hη hm hn hv hw x y he
  obtain ⟨a, b, hab⟩ := hstrict
  exact hab.ne (congrFun (congrFun hall a) b)

/-- Actual opposite root marks before a positive correlated mark
make the finite-recursion scalar bound strict at every pair of fields.
The two root masses may be zero. -/
theorem pairColeHopfIterate_lt_scalar_of_opposite_before_correlated
    (pre tail : List PairColeHopfLevel) (q r : PairColeHopfLevel)
    (hpre : ∀ p ∈ pre, 0 ≤ p.mass) (hq : 0 ≤ q.mass) (hr : 0 ≤ r.mass)
    (hkinds : (q.kind = .common ∧ r.kind = .antisymmetric) ∨
      (q.kind = .antisymmetric ∧ r.kind = .common))
    (hqv : q.variance ≠ 0) (hrv : r.variance ≠ 0) (htail : ∀ p ∈ tail, 0 ≤ p.mass)
    (hscalar : ∀ p ∈ pairColeHopfScalarLevels tail, p.1 ∈ Icc (0 : ℝ) 1)
    (hcor : ∃ p ∈ tail, p.kind ≠ .independent ∧ 0 < p.mass ∧ p.variance ≠ 0) (x y : ℝ) :
    pairColeHopfIterate (pre ++ q :: r :: tail)
      (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) x y <
      coleHopfIterateList (pairColeHopfScalarLevels (pre ++ q :: r :: tail)) (parisiLogCoshTerminal 0) x +
        coleHopfIterateList (pairColeHopfScalarLevels (pre ++ q :: r :: tail)) (parisiLogCoshTerminal 0) y := by
  have hL : ∀ x y, |parisiLogCoshTerminal 0 y - parisiLogCoshTerminal 0 x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0
  let A := coleHopfIterateList (pairColeHopfScalarLevels tail) (parisiLogCoshTerminal 0)
  have hAl := abs_coleHopfIterateList_sub_le (pairColeHopfScalarLevels tail) hL
  have hAl' : ∀ x y, |A y - A x| ≤ |y - x| := by simpa only [one_mul] using hAl
  let B := coleHopf r.scalar.1 r.variance A
  have hBl := abs_coleHopf_sub_le_of_lipschitz r.scalar.1
    (lipschitzWith_toNNReal_of_abs_sub_le hAl).continuous.measurable hAl r.variance
  have hBl' : ∀ x y, |B y - B x| ≤ |y - x| := by simpa only [one_mul] using hBl
  have hmono := pairColeHopfOperator_mono q
    (pairColeHopfOperator_lipschitz r (pairUnitLipschitz_sum hAl'))
    (pairUnitLipschitz_sum hBl')
    (pairColeHopfOperator_sum_le r hAl' (coleHopfIterateList_logCosh_even _) hr)
  have hqbound := pairColeHopfOperator_sum_le q hBl'
    (coleHopf_even (lipschitzWith_toNNReal_of_abs_sub_le hAl).continuous.measurable
      (coleHopfIterateList_logCosh_even _) r.scalar.1 r.variance) hq
  apply pairColeHopfIterate_prefix_lt_scalar pre (q :: r :: tail) hpre (fun a b => ?_) x y
  have hs : pairColeHopfOperator q (pairColeHopfOperator r (pairColeHopfIterate tail
      (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b))) a b <
      pairColeHopfOperator q (pairColeHopfOperator r (fun a b => A a + A b)) a b := by
    rcases hkinds with ⟨hqkind, hrkind⟩ | ⟨hqkind, hrkind⟩
    · simpa only [pairColeHopfOperator, hqkind, hrkind, neg_one_mul] using
        correlatedPairColeHopf_opposite_lt_of_exists_lt
          (pairColeHopfIterate_lipschitz tail (pairUnitLipschitz_sum (abs_parisiLogCoshTerminal_sub_le 0)))
          (pairUnitLipschitz_sum hAl') (pairColeHopfIterate_logCosh_le_scalar tail htail)
          (pairColeHopfIterate_exists_gap_of_correlated tail htail hscalar hcor)
          (η := 1) (Or.inl rfl) hq hr hqv hrv a b
    · simpa only [pairColeHopfOperator, hqkind, hrkind, neg_neg] using
        correlatedPairColeHopf_opposite_lt_of_exists_lt
          (pairColeHopfIterate_lipschitz tail (pairUnitLipschitz_sum (abs_parisiLogCoshTerminal_sub_le 0)))
          (pairUnitLipschitz_sum hAl') (pairColeHopfIterate_logCosh_le_scalar tail htail)
          (pairColeHopfIterate_exists_gap_of_correlated tail htail hscalar hcor)
          (η := -1) (Or.inr rfl) hq hr hqv hrv a b
  simpa only [pairColeHopfIterate, pairColeHopfScalarLevels, List.map_cons,
    coleHopfIterateList_cons, A, B, PairColeHopfLevel.scalar] using (hs.trans_le (hmono a b)).trans_le (hqbound a b)

theorem randomFieldPairColeHopfListValue_lt_scalar_of_opposite_before_correlated
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (pre tail : List PairColeHopfLevel) (q r : PairColeHopfLevel)
    (hpre : ∀ p ∈ pre, 0 ≤ p.mass) (hq : 0 ≤ q.mass) (hr : 0 ≤ r.mass)
    (hkinds : (q.kind = .common ∧ r.kind = .antisymmetric) ∨
      (q.kind = .antisymmetric ∧ r.kind = .common))
    (hqv : q.variance ≠ 0) (hrv : r.variance ≠ 0) (htail : ∀ p ∈ tail, 0 ≤ p.mass)
    (hscalar : ∀ p ∈ pairColeHopfScalarLevels tail, p.1 ∈ Icc (0 : ℝ) 1)
    (hcor : ∃ p ∈ tail, p.kind ≠ .independent ∧ 0 < p.mass ∧ p.variance ≠ 0) :
    randomFieldPairColeHopfListValue μh (pre ++ q :: r :: tail) <
      2 * randomFieldColeHopfListValue μh (pairColeHopfScalarLevels (pre ++ q :: r :: tail)) := by
  let l := pre ++ q :: r :: tail
  have hF := integrable_pairColeHopfIterate_externalField hμ l
  have hG := (integrable_coleHopfIterateList_externalField hμ (pairColeHopfScalarLevels l)).const_mul 2
  have hs (h : ℝ) : pairColeHopfIterate l
      (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) h h <
        2 * coleHopfIterateList (pairColeHopfScalarLevels l) (parisiLogCoshTerminal 0) h := by
    simpa only [two_mul] using pairColeHopfIterate_lt_scalar_of_opposite_before_correlated
      pre tail q r hpre hq hr hkinds hqv hrv htail hscalar hcor h h
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
