import SpinGlass.Parisi.Variational.ParisiColeHopfSwap
import SpinGlass.Parisi.Variational.ParisiSpatialThird
import SpinGlass.Parisi.Minimizer.Compact
import Mathlib.Data.List.Sort
import Mathlib.Data.List.OfFn

/-!
# Rearranging actual finite Cole-Hopf level lists

Adjacent mass swaps extend through every prefix of the recursion.
Insertion sorting therefore increases its value. Strict comparison
tracks inversions whose two variances are positive, as in Section 14.10.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

def parisiLevelMassOrder (p q : ℝ × ℝ≥0) : Prop := p.1 ≤ q.1

noncomputable instance : DecidableRel parisiLevelMassOrder := by
  intro p q
  unfold parisiLevelMassOrder
  infer_instance

instance : Std.Total parisiLevelMassOrder := ⟨fun p q => le_total p.1 q.1⟩

instance : IsTrans (ℝ × ℝ≥0) parisiLevelMassOrder :=
  ⟨fun _ _ _ hpq hqr => hpq.trans hqr⟩

theorem coleHopfIterateList_mono_of_lipschitz {A B : ℝ → ℝ} {L₁ L₂ : ℝ}
    (hA : ∀ x y, |A y - A x| ≤ L₁ * |y - x|)
    (hB : ∀ x y, |B y - B x| ≤ L₂ * |y - x|) (hAB : ∀ x, A x ≤ B x)
    (l : List (ℝ × ℝ≥0)) (x : ℝ) :
    coleHopfIterateList l A x ≤ coleHopfIterateList l B x := by
  induction l generalizing x with
  | nil => exact hAB x
  | cons p l ih =>
    have hAl := abs_coleHopfIterateList_sub_le l hA
    have hBl := abs_coleHopfIterateList_sub_le l hB
    simp only [coleHopfIterateList_cons]
    exact coleHopf_mono (HasLinearGrowth.of_lipschitz hAl)
      (lipschitzWith_toNNReal_of_abs_sub_le hAl).continuous.measurable
      (HasLinearGrowth.of_lipschitz hBl) (lipschitzWith_toNNReal_of_abs_sub_le hBl).continuous.measurable
      ih p.1 p.2 x

private theorem integral_lt_of_forall_lt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ x, f x < g x) : (∫ x, f x ∂μ) < ∫ x, g x ∂μ := by
  apply lt_of_le_of_ne (integral_mono hf hg (fun x => (hfg x).le))
  intro he
  have hae := (integral_eq_iff_of_ae_le hf hg (.of_forall fun x => (hfg x).le)).1 he
  obtain ⟨x, hx⟩ := hae.exists
  exact (hfg x).ne hx

/-- Strict pointwise terminal comparison passes through every
nonnegative Cole-Hopf mass, including the genuine zero-mass branch. -/
theorem coleHopf_lt_of_forall_lt {A B : ℝ → ℝ} {L₁ L₂ : ℝ}
    (hA : ∀ x y, |A y - A x| ≤ L₁ * |y - x|)
    (hB : ∀ x y, |B y - B x| ≤ L₂ * |y - x|) (hAB : ∀ x, A x < B x)
    {m : ℝ} (hm : 0 ≤ m) (v : ℝ≥0) (x : ℝ) : coleHopf m v A x < coleHopf m v B x := by
  have hAg := HasLinearGrowth.of_lipschitz hA
  have hBg := HasLinearGrowth.of_lipschitz hB
  have hAm := (lipschitzWith_toNNReal_of_abs_sub_le hA).continuous.measurable
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
  rcases eq_or_lt_of_le hm with hm0 | hmpos
  · have hm0' : m = 0 := hm0.symm
    subst m
    rw [coleHopf_zero, coleHopf_zero]
    exact integral_lt_of_forall_lt
      ((hAg.comp_add_const x).toHasExpGrowth.integrable_gaussianReal
        (hAm.comp (measurable_const.add measurable_id)).aestronglyMeasurable)
      ((hBg.comp_add_const x).toHasExpGrowth.integrable_gaussianReal
        (hBm.comp (measurable_const.add measurable_id)).aestronglyMeasurable) (fun z => hAB _)
  · have hI := integral_lt_of_forall_lt (integrable_exp_mul_comp_add hAg hAm m v x)
      (integrable_exp_mul_comp_add hBg hBm m v x)
      (fun z => Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left (hAB (x + z)) hmpos))
    rw [coleHopf_of_ne hmpos.ne', coleHopf_of_ne hmpos.ne']
    exact mul_lt_mul_of_pos_left (Real.log_lt_log (integral_exp_mul_comp_add_pos hAg hAm m v x) hI)
      (one_div_pos.2 hmpos)

theorem coleHopfIterateList_lt_of_lipschitz {A B : ℝ → ℝ} {L₁ L₂ : ℝ}
    (hA : ∀ x y, |A y - A x| ≤ L₁ * |y - x|)
    (hB : ∀ x y, |B y - B x| ≤ L₂ * |y - x|) (hAB : ∀ x, A x < B x)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p ∈ l, 0 ≤ p.1) (x : ℝ) :
    coleHopfIterateList l A x < coleHopfIterateList l B x := by
  induction l generalizing x with
  | nil => exact hAB x
  | cons p l ih =>
    have hml : ∀ q ∈ l, 0 ≤ q.1 := fun q hq => hm q (List.mem_cons_of_mem _ hq)
    simp only [coleHopfIterateList_cons]
    exact coleHopf_lt_of_forall_lt (abs_coleHopfIterateList_sub_le l hA)
      (abs_coleHopfIterateList_sub_le l hB) (ih hml) (hm p (List.mem_cons_self)) p.2 x

/-- Inserting one mass into a list by adjacent swaps increases the
actual recursion at every field value, including zero masses and variances. -/
theorem coleHopfIterateList_orderedInsert_le {A : ℝ → ℝ}
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) (p : ℝ × ℝ≥0) (l : List (ℝ × ℝ≥0)) :
    (∀ q ∈ l, 0 ≤ q.1) → 0 ≤ p.1 → ∀ x : ℝ,
      coleHopf p.1 p.2 (coleHopfIterateList l A) x ≤
        coleHopfIterateList (List.orderedInsert parisiLevelMassOrder p l) A x := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  induction l with
  | nil => intro _ _ x; rfl
  | cons q l ih =>
    intro hms hp x
    have hml : ∀ r ∈ l, 0 ≤ r.1 := fun r hr => hms r (List.mem_cons_of_mem _ hr)
    have hql : 0 ≤ q.1 := hms q (List.mem_cons_self)
    by_cases hpq : parisiLevelMassOrder p q
    · rw [List.orderedInsert_cons_of_le parisiLevelMassOrder l hpq, coleHopfIterateList_cons]
      rfl
    · rw [List.orderedInsert_of_not_le parisiLevelMassOrder l hpq]
      have htail := abs_coleHopfIterateList_sub_le l hL
      have htailm := (lipschitzWith_toNNReal_of_abs_sub_le htail).continuous.measurable
      have hprefix := coleHopfIterateList_mono_of_lipschitz
        (abs_coleHopfIterateList_sub_le (p :: l) hL)
        (abs_coleHopfIterateList_sub_le (List.orderedInsert parisiLevelMassOrder p l) hL)
        (ih hml hp) [q] x
      simp only [coleHopfIterateList_cons, coleHopfIterateList_nil] at hprefix ⊢
      exact (coleHopf_swap_le htailm (by simpa only [one_mul] using htail) hql
        (le_of_not_ge hpq) p.2 q.2 x).trans hprefix

/-- Sorting every mass by insertion sorting increases the actual
finite recursion. This is the non-strict rearrangement in Lemma 14.10.6. -/
theorem coleHopfIterateList_le_insertionSort {A : ℝ → ℝ}
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) (l : List (ℝ × ℝ≥0)) :
    (∀ p ∈ l, 0 ≤ p.1) → ∀ x : ℝ,
      coleHopfIterateList l A x ≤ coleHopfIterateList (List.insertionSort parisiLevelMassOrder l) A x := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  induction l with
  | nil => intro _ x; rfl
  | cons p l ih =>
    intro hm x
    have hml : ∀ q ∈ l, 0 ≤ q.1 := fun q hq => hm q (List.mem_cons_of_mem _ hq)
    have hms : ∀ q ∈ List.insertionSort parisiLevelMassOrder l, 0 ≤ q.1 :=
      fun q hq => hml q ((List.mem_insertionSort parisiLevelMassOrder).1 hq)
    have hp := hm p (List.mem_cons_self)
    have hprefix := coleHopfIterateList_mono_of_lipschitz (abs_coleHopfIterateList_sub_le l hL)
      (abs_coleHopfIterateList_sub_le (List.insertionSort parisiLevelMassOrder l) hL) (ih hml) [p] x
    simp only [coleHopfIterateList_cons, coleHopfIterateList_nil] at hprefix
    rw [List.insertionSort_cons, coleHopfIterateList_cons]
    exact hprefix.trans (coleHopfIterateList_orderedInsert_le hA p _ hms hp x)

/-- Strict convexity of the actual log-cosh suffix in list form.
The mass list may be unordered and its variances may vanish. -/
theorem coleHopfIterateList_logCosh_strictConvex (l : List (ℝ × ℝ≥0))
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0 : ℝ) 1) :
    StrictConvexOn ℝ univ (coleHopfIterateList l (parisiLogCoshTerminal 0)) := by
  let ms : Fin l.length → ℝ := fun i => (l.get i).1
  let vs : Fin l.length → ℝ≥0 := fun i => (l.get i).2
  have hmass : ∀ i, ms i ∈ Icc (0 : ℝ) 1 := fun i => hm _ (List.get_mem _ _)
  have hc := coleHopfIterate_logCosh_strictConvex ms vs hmass
  rw [coleHopfIterate_eq_list] at hc
  have he : List.ofFn (fun i => (ms i, vs i)) = l := by
    dsimp only [ms, vs]
    exact List.ofFn_get l
  rw [he] at hc
  exact hc

/-- Inserting an active level past a smaller active mass strictly
increases the actual log-cosh recursion. Sortedness ensures that the
smaller witness lies on the adjacent insertion path. -/
theorem coleHopfIterateList_orderedInsert_lt (p : ℝ × ℝ≥0) (l : List (ℝ × ℝ≥0))
    (hp : p.1 ∈ Icc (0 : ℝ) 1) (hpv : p.2 ≠ 0) :
    (∀ q ∈ l, q.1 ∈ Icc (0 : ℝ) 1) → List.Pairwise parisiLevelMassOrder l →
    (∃ q ∈ l, q.1 < p.1 ∧ q.2 ≠ 0) → ∀ x : ℝ,
      coleHopf p.1 p.2 (coleHopfIterateList l (parisiLogCoshTerminal 0)) x <
        coleHopfIterateList (List.orderedInsert parisiLevelMassOrder p l) (parisiLogCoshTerminal 0) x := by
  have hL : ∀ x y, |parisiLogCoshTerminal 0 y - parisiLogCoshTerminal 0 x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0
  have hA : ∀ x y, |parisiLogCoshTerminal 0 y - parisiLogCoshTerminal 0 x| ≤ |y - x| :=
    abs_parisiLogCoshTerminal_sub_le 0
  induction l with
  | nil =>
    intro _ _ hq _
    obtain ⟨q, hq, _⟩ := hq
    exact (List.not_mem_nil hq).elim
  | cons q l ih =>
    intro hm hs hq x
    have hml : ∀ r ∈ l, r.1 ∈ Icc (0 : ℝ) 1 := fun r hr => hm r (List.mem_cons_of_mem _ hr)
    have hmq := hm q (List.mem_cons_self)
    have hsl := (List.pairwise_cons.1 hs).2
    by_cases hpq : parisiLevelMassOrder p q
    · obtain ⟨r, hr, hrp, _⟩ := hq
      rcases List.mem_cons.1 hr with rfl | hr
      · exact (not_lt_of_ge hpq hrp).elim
      · have hqr := (List.pairwise_cons.1 hs).1 r hr
        exact (not_lt_of_ge (le_trans hpq hqr) hrp).elim
    · rw [List.orderedInsert_of_not_le parisiLevelMassOrder l hpq]
      have htail := abs_coleHopfIterateList_sub_le l hL
      have htailm := (lipschitzWith_toNNReal_of_abs_sub_le htail).continuous.measurable
      have hbefore := abs_coleHopfIterateList_sub_le (p :: l) hL
      have hafter := abs_coleHopfIterateList_sub_le (List.orderedInsert parisiLevelMassOrder p l) hL
      simp only [coleHopfIterateList_cons]
      by_cases hqv : q.2 = 0
      · have hwitness : ∃ r ∈ l, r.1 < p.1 ∧ r.2 ≠ 0 := by
          obtain ⟨r, hr, hrp, hrv⟩ := hq
          rcases List.mem_cons.1 hr with rfl | hr
          · exact (hrv hqv).elim
          · exact ⟨r, hr, hrp, hrv⟩
        have hprefix := coleHopf_lt_of_forall_lt hbefore hafter (ih hml hsl hwitness) hmq.1 q.2 x
        exact (coleHopf_swap_le htailm (by simpa only [one_mul] using htail) hmq.1
          (le_of_not_ge hpq) p.2 q.2 x).trans_lt hprefix
      · have hprefix := coleHopfIterateList_mono_of_lipschitz hbefore hafter
          (coleHopfIterateList_orderedInsert_le hA p l (fun r hr => (hml r hr).1) hp.1) [q] x
        simp only [coleHopfIterateList_cons, coleHopfIterateList_nil] at hprefix
        exact (coleHopf_swap_lt htailm (by simpa only [one_mul] using htail)
          (coleHopfIterateList_logCosh_strictConvex l hml) hmq.1 (lt_of_not_ge hpq) hpv hqv x).trans_le hprefix

/-- The active-level order ignores only deterministic zero-variance
levels. It is exactly the mass-order conclusion needed in (14.387). -/
def parisiActiveLevelMassOrder (p q : ℝ × ℝ≥0) : Prop := p.2 = 0 ∨ q.2 = 0 ∨ p.1 ≤ q.1

/-- An inversion between two positive-variance levels makes sorting
strict at every field value. Mass zero is included in the equality analysis. -/
theorem coleHopfIterateList_insertionSort_lt_of_active_inversion (l : List (ℝ × ℝ≥0)) :
    (∀ p ∈ l, p.1 ∈ Icc (0 : ℝ) 1) → ¬List.Pairwise parisiActiveLevelMassOrder l → ∀ x : ℝ,
      coleHopfIterateList l (parisiLogCoshTerminal 0) x <
        coleHopfIterateList (List.insertionSort parisiLevelMassOrder l) (parisiLogCoshTerminal 0) x := by
  classical
  have hL : ∀ x y, |parisiLogCoshTerminal 0 y - parisiLogCoshTerminal 0 x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0
  have hA : ∀ x y, |parisiLogCoshTerminal 0 y - parisiLogCoshTerminal 0 x| ≤ |y - x| :=
    abs_parisiLogCoshTerminal_sub_le 0
  induction l with
  | nil => intro _ hn _; exact (hn (List.Pairwise.nil)).elim
  | cons p l ih =>
    intro hm hn x
    have hml : ∀ q ∈ l, q.1 ∈ Icc (0 : ℝ) 1 := fun q hq => hm q (List.mem_cons_of_mem _ hq)
    have hms : ∀ q ∈ List.insertionSort parisiLevelMassOrder l, q.1 ∈ Icc (0 : ℝ) 1 :=
      fun q hq => hml q ((List.mem_insertionSort parisiLevelMassOrder).1 hq)
    have hp := hm p (List.mem_cons_self)
    have hbefore := abs_coleHopfIterateList_sub_le l hL
    have hafter := abs_coleHopfIterateList_sub_le (List.insertionSort parisiLevelMassOrder l) hL
    rw [List.insertionSort_cons, coleHopfIterateList_cons]
    by_cases ht : List.Pairwise parisiActiveLevelMassOrder l
    · have hhead : ¬∀ q ∈ l, parisiActiveLevelMassOrder p q :=
        fun h => hn (List.pairwise_cons.2 ⟨h, ht⟩)
      push Not at hhead
      obtain ⟨q, hq, hpq⟩ := hhead
      have hpv : p.2 ≠ 0 := fun h => hpq (Or.inl h)
      have hqv : q.2 ≠ 0 := fun h => hpq (Or.inr (Or.inl h))
      have hqp : q.1 < p.1 := lt_of_not_ge (fun h => hpq (Or.inr (Or.inr h)))
      have hprefix := coleHopfIterateList_mono_of_lipschitz hbefore hafter
        (coleHopfIterateList_le_insertionSort hA l (fun q hq => (hml q hq).1)) [p] x
      simp only [coleHopfIterateList_cons, coleHopfIterateList_nil] at hprefix
      exact hprefix.trans_lt (coleHopfIterateList_orderedInsert_lt p _ hp hpv hms
        (List.pairwise_insertionSort parisiLevelMassOrder l)
        ⟨q, (List.mem_insertionSort parisiLevelMassOrder).2 hq, hqp, hqv⟩ x)
    · have hprefix := coleHopf_lt_of_forall_lt hbefore hafter (ih hml ht) hp.1 p.2 x
      exact hprefix.trans_le (coleHopfIterateList_orderedInsert_le hA p _
        (fun q hq => (hms q hq).1) hp.1 x)

/-- Equality of the actual sorted and unsorted log-cosh recursion
forces nondecreasing masses at every pair of positive-variance levels. -/
theorem parisiActiveLevelMassOrder_of_coleHopfIterateList_sort_eq
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p ∈ l, p.1 ∈ Icc (0 : ℝ) 1) (x : ℝ)
    (he : coleHopfIterateList l (parisiLogCoshTerminal 0) x =
      coleHopfIterateList (List.insertionSort parisiLevelMassOrder l) (parisiLogCoshTerminal 0) x) :
    List.Pairwise parisiActiveLevelMassOrder l := by
  by_contra hn
  exact (coleHopfIterateList_insertionSort_lt_of_active_inversion l hm hn x).ne he

/-- The actual one-site expectation of a finite Gaussian Cole-Hopf
list. Root expectation levels are represented by genuine mass-zero entries. -/
noncomputable def randomFieldColeHopfListValue (μh : Measure ℝ) (l : List (ℝ × ℝ≥0)) : ℝ :=
  ∫ h, coleHopfIterateList l (parisiLogCoshTerminal 0) h ∂μh

theorem integrable_coleHopfIterateList_externalField {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (l : List (ℝ × ℝ≥0)) :
    Integrable (coleHopfIterateList l (parisiLogCoshTerminal 0)) μh := by
  let F := coleHopfIterateList l (parisiLogCoshTerminal 0)
  have hL : ∀ x y, |parisiLogCoshTerminal 0 y - parisiLogCoshTerminal 0 x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0
  have hF := abs_coleHopfIterateList_sub_le l hL
  apply ((integrable_const |F 0|).add hμ.abs).mono'
    (lipschitzWith_toNNReal_of_abs_sub_le hF).continuous.measurable.aestronglyMeasurable
  refine .of_forall fun h => ?_
  change |F h| ≤ |F 0| + |h|
  have hh := hF 0 h
  have ha := abs_sub_abs_le_abs_sub (F h) (F 0)
  simp only [sub_zero, one_mul] at hh
  linarith

/-- The non-strict finite rearrangement survives the actual
external-field expectation with only a finite first field moment. -/
theorem randomFieldColeHopfListValue_le_insertionSort {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (l : List (ℝ × ℝ≥0)) (hm : ∀ p ∈ l, 0 ≤ p.1) :
    randomFieldColeHopfListValue μh l ≤
      randomFieldColeHopfListValue μh (List.insertionSort parisiLevelMassOrder l) := by
  unfold randomFieldColeHopfListValue
  exact integral_mono (integrable_coleHopfIterateList_externalField hμ l)
    (integrable_coleHopfIterateList_externalField hμ _) (fun h =>
      coleHopfIterateList_le_insertionSort (abs_parisiLogCoshTerminal_sub_le 0) l hm h)

/-- An active mass inversion yields a strict gap in the actual
one-site field average, without an exponential field moment. -/
theorem randomFieldColeHopfListValue_insertionSort_lt_of_active_inversion
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p ∈ l, p.1 ∈ Icc (0 : ℝ) 1)
    (hn : ¬List.Pairwise parisiActiveLevelMassOrder l) :
    randomFieldColeHopfListValue μh l <
      randomFieldColeHopfListValue μh (List.insertionSort parisiLevelMassOrder l) := by
  exact integral_lt_of_forall_lt (integrable_coleHopfIterateList_externalField hμ l)
    (integrable_coleHopfIterateList_externalField hμ _)
    (coleHopfIterateList_insertionSort_lt_of_active_inversion l hm hn)

/-- Equality after field averaging still forces nondecreasing
effective masses at all positive-variance levels, the scalar order
condition in (14.387). -/
theorem parisiActiveLevelMassOrder_of_randomFieldColeHopfList_sort_eq
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p ∈ l, p.1 ∈ Icc (0 : ℝ) 1)
    (he : randomFieldColeHopfListValue μh l =
      randomFieldColeHopfListValue μh (List.insertionSort parisiLevelMassOrder l)) :
    List.Pairwise parisiActiveLevelMassOrder l := by
  by_contra hn
  exact (randomFieldColeHopfListValue_insertionSort_lt_of_active_inversion hμ l hm hn).ne he

/-- The original scalar Parisi levels, including the genuine
zero-mass root expectation and terminal mass one. -/
noncomputable def parisiFullColeHopfLevels (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) : List (ℝ × ℝ≥0) :=
  List.ofFn (fun i : Fin (k + 2) => ((Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms)) i, parisiAllVars ξ qs i))

theorem parisiFullColeHopfLevels_sorted (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) :
    List.Pairwise parisiLevelMassOrder (parisiFullColeHopfLevels ξ ms qs) := by
  have hmass (i : Fin (k + 2)) : (Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms)) i = mExt ms i.val := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Fin.val_zero, mExt_zero]
    · rw [Fin.cons_succ, parisiLevelMasses_apply]
      rfl
  unfold parisiFullColeHopfLevels
  apply List.pairwise_ofFn.2
  intro i j hij
  change (Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms)) i ≤
    (Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms)) j
  rw [hmass, hmass]
  exact hm.monotone_mExt (Fin.le_iff_val_le_val.1 hij.le)

/-- The list-value comparator is identified with the actual original
closed Parisi recursion, including its external-field expectation. -/
theorem randomFieldColeHopfListValue_parisiFull_eq (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    randomFieldColeHopfListValue μh (parisiFullColeHopfLevels ξ ms qs) = ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  unfold randomFieldColeHopfListValue parisiFullColeHopfLevels
  apply integral_congr_ae (.of_forall fun h => ?_)
  rw [closedParisiX₀_translate, coleHopfIterate_eq_list]

end SpinGlass
