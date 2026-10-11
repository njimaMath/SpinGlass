import SpinGlass.Parisi.Variational.ParisiMVariation

/-!
# Mass insertion in the initial overlap interval

The initial interval in (14.225)-(14.240) starts at the fixed overlap zero.
Its original mass is zero, so its split precedes every free overlap and mass.
The constructors here complement the two nonroot orientations.
-/

open MeasureTheory ProbabilityTheory Set

namespace SpinGlass

/-- The mass on the right part of the initial interval `[0,q₁]`. -/
def splitParisiRootMass {k : ℕ} (ms : Fin k → ℝ) (m : ℝ) : Fin (k + 1) → ℝ :=
  Fin.cons m ms

/-- Split the initial interval by inserting an overlap before `q₁`. -/
def splitParisiRootOverlap {k : ℕ} (qs : Fin (k + 1) → ℝ) (u : ℝ) :
    Fin (k + 2) → ℝ := Fin.cons u qs

/-- Inserting a first free overlap shifts every later extended overlap by one. -/
theorem qExt_splitParisiRootOverlap_succ {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (u : ℝ) (n : ℕ) :
    qExt (splitParisiRootOverlap qs u) (n + 2) = qExt qs (n + 1) := by
  by_cases hn : n < k + 1
  · rw [qExt_succ_of_lt _ (by omega : n + 1 < k + 2), qExt_succ_of_lt qs hn]
    change Fin.cons (α := fun _ => ℝ) u qs (⟨n, hn⟩ : Fin (k + 1)).succ = qs ⟨n, hn⟩
    exact Fin.cons_succ _ _ _
  · rw [qExt_of_le _ (by omega), qExt_of_le qs (by omega)]

/-- The root mass insertion agrees with insertion at array coordinate zero. -/
theorem splitParisiRootMass_eq_left {k : ℕ} (ms : Fin k → ℝ) (m : ℝ) :
    splitParisiRootMass ms m = splitParisiMassLeft ms 0 m := by
  simp only [splitParisiRootMass, splitParisiMassLeft, Fin.insertNth_zero']

/-- The root overlap insertion stays in the closed overlap domain. -/
theorem splitParisiRootOverlap_mem_domain {k : ℕ} {qs : Fin (k + 1) → ℝ}
    (hq : qs ∈ parisiOverlapDomain k) {u : ℝ} (hu : 0 ≤ u ∧ u ≤ qs 0) :
    splitParisiRootOverlap qs u ∈ parisiOverlapDomain (k + 1) := by
  obtain ⟨hmono, hq0, hq1⟩ := mem_parisiOverlapDomain_iff.1 hq
  refine mem_parisiOverlapDomain_iff.2 ⟨?_, hu.1, ?_⟩
  · simpa only [splitParisiRootOverlap, Fin.insertNth_zero'] using
      Fin.insertNth_zero_monotone hmono u hu.2
  · change Fin.cons (α := fun _ => ℝ) u qs (Fin.last k).succ ≤ 1
    simpa only [Fin.cons_succ] using hq1

/-- The inserted root mass lies between the fixed zero mass and `m₁`. -/
theorem splitParisiRootMass_mem_domain {k : ℕ} {ms : Fin k → ℝ}
    (hm : ms ∈ parisiMassDomain k) {m : ℝ} (hmp : 0 ≤ m ∧ m ≤ mExt ms 1) :
    splitParisiRootMass ms m ∈ parisiMassDomain (k + 1) := by
  rw [splitParisiRootMass_eq_left]
  apply splitParisiMassLeft_mem_domain hm 0
  simpa only [Fin.val_zero, mExt_zero, zero_add] using hmp

/-- The initial interval split is a competitor even at zero or unit mass. -/
theorem splitParisiRoot_mem_parameterDomain {k : ℕ}
    {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ}
    (hm : ms ∈ parisiMassDomain k) (hq : qs ∈ parisiOverlapDomain k)
    {m u : ℝ} (hmp : 0 ≤ m ∧ m ≤ mExt ms 1) (hu : 0 ≤ u ∧ u ≤ qs 0) :
    (splitParisiRootMass ms m, splitParisiRootOverlap qs u) ∈
      parisiParameterDomain (k + 1) :=
  ⟨splitParisiRootMass_mem_domain hm hmp, splitParisiRootOverlap_mem_domain hq hu⟩

/-- At the old first overlap, the new and old first coordinates coincide. -/
theorem splitParisiRootOverlap_right_eq {k : ℕ} (qs : Fin (k + 1) → ℝ) :
    splitParisiRootOverlap qs (qs 0) = splitParisiOverlap qs 0 (qs 0) := by
  unfold splitParisiRootOverlap splitParisiOverlap
  conv_rhs => arg 3; rw [← Fin.cons_self_tail qs]
  rw [Fin.insertNth_succ_cons, Fin.insertNth_zero', Fin.cons_self_tail]

/-- The empty inserted root interval preserves the closed functional. -/
theorem closedRandomFieldParisiFunctional_split_root_right_endpoint
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (m : ℝ) :
    closedRandomFieldParisiFunctional μh ξ
      (splitParisiRootMass ms m) (splitParisiRootOverlap qs (qs 0)) =
      closedRandomFieldParisiFunctional μh ξ ms qs := by
  rw [splitParisiRootMass_eq_left, splitParisiRootOverlap_right_eq]
  exact closedRandomFieldParisiFunctional_split_left_endpoint μh ms qs 0 m

/-- Moving the inserted first overlap to the old first overlap is a root update. -/
theorem qUpdate_splitParisiRootOverlap {k : ℕ} (qs : Fin (k + 1) → ℝ) (u v : ℝ) :
    qUpdate (splitParisiRootOverlap qs u) 0 v = splitParisiRootOverlap qs v := by
  simpa only [splitParisiMassLeft, Fin.insertNth_zero', splitParisiRootOverlap, qUpdate] using
    update_splitParisiMassLeft qs 0 u v

/-- Matching the old root mass zero merges the two plain Gaussian averages.
This proves (14.237) for the first interval without assuming positive mass. -/
theorem closedRandomFieldParisiFunctional_split_root_zero_mass
    (μh : Measure ℝ) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hq : qs ∈ parisiOverlapDomain k) {u : ℝ} (hu : 0 ≤ u ∧ u ≤ qs 0) :
    closedRandomFieldParisiFunctional μh ξ
      (splitParisiRootMass ms 0) (splitParisiRootOverlap qs u) =
      closedRandomFieldParisiFunctional μh ξ ms qs := by
  have he := closedRandomFieldParisiFunctional_first_zero_mass_eq μh hξ
    (splitParisiRootMass ms 0) (splitParisiRootOverlap qs u)
    (splitParisiRootOverlap_mem_domain hq hu) (by simp only [splitParisiRootMass, Fin.cons_zero])
  have hfirst : splitParisiRootOverlap qs u 1 = qs 0 := by rfl
  rw [hfirst, qUpdate_splitParisiRootOverlap,
    closedRandomFieldParisiFunctional_split_root_right_endpoint] at he
  exact he.symm

/-- The global Parisi infimum bounds the root split of (14.226). -/
theorem randomFieldParisiInf_le_split_root
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ)
    {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ}
    (hm : ms ∈ parisiMassDomain k) (hq : qs ∈ parisiOverlapDomain k)
    {m u : ℝ} (hmp : 0 ≤ m ∧ m ≤ mExt ms 1) (hu : 0 ≤ u ∧ u ≤ qs 0) :
    randomFieldParisiInf μh ξ ≤ closedRandomFieldParisiFunctional μh ξ
      (splitParisiRootMass ms m) (splitParisiRootOverlap qs u) :=
  randomFieldParisiInf_le_closedRandomFieldParisiFunctional hμ hξ
    (splitParisiRoot_mem_parameterDomain hm hq hmp hu)

/-- The MIN tolerance compares the original value with the root split,
using the global infimum across the different level counts. -/
theorem randomFieldParisiFunctional_sub_lt_split_root_of_near_inf
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ)
    {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ} {ε : ℝ}
    (hm : ms ∈ parisiMassDomain k) (hq : qs ∈ parisiOverlapDomain k)
    (hnear : randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε)
    {m u : ℝ} (hmp : 0 ≤ m ∧ m ≤ mExt ms 1) (hu : 0 ≤ u ∧ u ≤ qs 0) :
    randomFieldParisiFunctional μh ξ ms qs - ε < closedRandomFieldParisiFunctional μh ξ
      (splitParisiRootMass ms m) (splitParisiRootOverlap qs u) :=
  randomFieldParisiFunctional_sub_lt_closed_of_near_inf hμ hξ hnear
    (splitParisiRoot_mem_parameterDomain hm hq hmp hu)

/-- The actual root inserted-mass derivative, including its theta correction. -/
noncomputable def splitParisiRootMassDeriv (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (u m : ℝ) : ℝ :=
  randomFieldParisiMassMoment μh ξ (splitParisiRootMass ms 0)
    (splitParisiRootOverlap qs u) 0 m - (1 / 2) *
      (parisiTheta ξ (qs 0) - parisiTheta ξ u)

/-- Differentiate the root mass within `[0,1]`. There are no positive-mass
prefix levels to assume in this first-interval case of (14.230). -/
theorem hasDerivWithinAt_closedRandomFieldParisiFunctional_split_root_mass
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (u : ℝ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun b => closedRandomFieldParisiFunctional μh ξ
        (splitParisiRootMass ms b) (splitParisiRootOverlap qs u))
      (splitParisiRootMassDeriv μh ξ ms qs u m) (Icc (0 : ℝ) 1) m := by
  have hd := hasDerivWithinAt_closedRandomFieldParisiFunctional_mass_update hμ ξ
    (splitParisiRootMass ms 0) (splitParisiRootOverlap qs u) 0
    (fun p => Fin.elim0 p) (fun p => Fin.elim0 p) hm
  have hu : qExt (splitParisiRootOverlap qs u) 1 = u := by
    simp [splitParisiRootOverlap, qExt_succ_of_lt]
  have hq : qExt (splitParisiRootOverlap qs u) 2 = qs 0 := by
    rw [qExt_succ_of_lt _ (by omega : 1 < k + 2)]
    rfl
  simpa only [splitParisiRootMass_eq_left, update_splitParisiMassLeft, Fin.val_zero,
    zero_add, hu, hq, splitParisiRootMassDeriv] using hd

/-- At the upper admissible inserted root mass, the adjacent matching layers
merge into the original functional with its first overlap changed to u.
This supplies the endpoint comparison in (14.264), also when k=0 and B=1. -/
theorem closedRandomFieldParisiFunctional_split_root_upper_mass
    (μh : Measure ℝ) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hq : qs ∈ parisiOverlapDomain k) {u : ℝ} (hu : 0 ≤ u ∧ u ≤ qs 0) :
    closedRandomFieldParisiFunctional μh ξ
        (splitParisiRootMass ms (mExt ms 1)) (splitParisiRootOverlap qs u) =
      closedRandomFieldParisiFunctional μh ξ ms (qUpdate qs 0 u) := by
  let r : Fin (k + 2) := (0 : Fin (k + 1)).succ
  have hmass : mExt (splitParisiRootMass ms (mExt ms 1)) r.val =
      mExt (splitParisiRootMass ms (mExt ms 1)) (r.val + 1) := by
    change mExt (Fin.cons (mExt ms 1) ms) 1 = mExt (Fin.cons (mExt ms 1) ms) (0 + 2)
    rw [mExt_one, Fin.cons_zero, mExt_succ_tail, Fin.tail_cons]
  have hfirst : qExt qs 1 = qs 0 := by simp [qExt]
  obtain ⟨hmono, hq0, hq1⟩ := mem_parisiOverlapDomain_iff.1 hq
  have hnext : qs 0 ≤ qExt qs 2 := by
    rw [← hfirst]
    exact qExt_le_succ hmono hq0 hq1 (by omega)
  have hbounds : qExt (splitParisiRootOverlap qs u) r.val ≤ u ∧
      u ≤ qExt (splitParisiRootOverlap qs u) (r.val + 2) := by
    change qExt (splitParisiRootOverlap qs u) 1 ≤ u ∧
      u ≤ qExt (splitParisiRootOverlap qs u) (1 + 2)
    have hleft : qExt (splitParisiRootOverlap qs u) 1 = u := by
      simp [qExt, splitParisiRootOverlap]
    have hright : qExt (splitParisiRootOverlap qs u) (1 + 2) = qExt qs 2 := by
      exact qExt_splitParisiRootOverlap_succ qs u 1
    rw [hleft, hright]
    exact ⟨le_rfl, hu.2.trans hnext⟩
  have he := closedRandomFieldParisiFunctional_qUpdate_eq_of_equal_mass μh hξ
    (splitParisiRootMass ms (mExt ms 1)) (splitParisiRootOverlap qs u)
    (splitParisiRootOverlap_mem_domain hq hu) r u hmass hbounds
  have hqs : qUpdate (splitParisiRootOverlap qs u) r u =
      splitParisiRootOverlap (qUpdate qs 0 u) u := by
    unfold qUpdate splitParisiRootOverlap
    exact (Fin.cons_update (α := fun _ => ℝ) u qs 0 u).symm
  rw [hqs] at he
  have hend := closedRandomFieldParisiFunctional_split_root_right_endpoint
    μh ξ ms (qUpdate qs 0 u) (mExt ms 1)
  rw [qUpdate_self] at hend
  exact he.symm.trans hend

/-- Fixed-level overlap minimality compares the upper root mass endpoint
with the matching-mass value. This is the short-interval endpoint input to
the square-root mass estimate (14.264); it also covers the empty mass array. -/
theorem closedRandomFieldParisiFunctional_split_root_zero_le_upper_of_isMin
    {μh : Measure ℝ} {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ}
    (hm : ParisiMAdmissible ms) (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    {u : ℝ} (hu : 0 ≤ u ∧ u ≤ qs 0) :
    closedRandomFieldParisiFunctional μh ξ
        (splitParisiRootMass ms 0) (splitParisiRootOverlap qs u) ≤
      closedRandomFieldParisiFunctional μh ξ
        (splitParisiRootMass ms (mExt ms 1)) (splitParisiRootOverlap qs u) := by
  have hq : qs ∈ parisiOverlapDomain k :=
    mem_parisiOverlapDomain_iff.2 ⟨hmin.1.1.monotone, hmin.1.2.1, hmin.1.2.2⟩
  rw [closedRandomFieldParisiFunctional_split_root_zero_mass μh hξ ms qs hq hu,
    closedRandomFieldParisiFunctional_split_root_upper_mass μh hξ ms qs hq hu,
    closedRandomFieldParisiFunctional_eq μh ξ ms qs hm,
    closedRandomFieldParisiFunctional_eq μh ξ ms (qUpdate qs 0 u) hm]
  refine hmin.le_qUpdate 0 hu.1 (hu.2.trans (hmin.1.mem_Icc 0).2) ?_ ?_
  · intro p hp
    have : p.val < 0 := hp
    omega
  · intro p hp
    exact hu.2.trans_lt (hmin.1.1 hp)

end SpinGlass
