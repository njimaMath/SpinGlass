import SpinGlass.Parisi.Minimizer.QVariation.ColeHopf

/-!
# Parameters

Overlap updates, admissibility, and fixed-mass minimizers.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

/-! ### The `q_r`-dependent part of the Parisi functional -/

/-- Replace one free overlap coordinate. A `Fin (k + 1)` index `r` represents Talagrand's
coordinate `q_{r+1}`. -/
def qUpdate {k : ℕ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : ℝ) :
    Fin (k + 1) → ℝ :=
  Function.update qs r u

lemma qUpdate_eq_of_eq {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) {u : ℝ} (hu : qs r = u) : qUpdate qs r u = qs := by
  subst u
  funext p
  simp [qUpdate]

@[simp] lemma qUpdate_self {k : ℕ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : ℝ) :
    qUpdate qs r u r = u := by
  simp [qUpdate]

@[simp] lemma qUpdate_of_ne {k : ℕ} (qs : Fin (k + 1) → ℝ) {r p : Fin (k + 1)} (u : ℝ)
    (hpr : p ≠ r) : qUpdate qs r u p = qs p := by
  simp [qUpdate, hpr]

lemma qExt_qUpdate_succ {k : ℕ} (qs : Fin (k + 1) → ℝ) (r p : Fin (k + 1)) (u : ℝ) :
    qExt (qUpdate qs r u) (p.val + 1) = if p = r then u else qExt qs (p.val + 1) := by
  rw [qExt_succ_of_lt (qUpdate qs r u) p.isLt, qExt_succ_of_lt qs p.isLt]
  by_cases hpr : p = r
  · subst p
    simp [qUpdate]
  · simp [qUpdate, hpr]

@[simp] lemma qExt_qUpdate_self {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (u : ℝ) : qExt (qUpdate qs r u) (r.val + 1) = u := by
  rw [qExt_qUpdate_succ]
  simp

lemma qExt_qUpdate_of_lt {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (u : ℝ) {n : ℕ} (hn : n < r.val + 1) :
    qExt (qUpdate qs r u) n = qExt qs n := by
  rcases n with _ | n
  · simp
  · have hnlt : n < k + 1 := by omega
    let p : Fin (k + 1) := ⟨n, hnlt⟩
    rw [show n + 1 = p.val + 1 by rfl, qExt_qUpdate_succ]
    rw [if_neg (by
      intro hpr
      have : n = r.val := congrArg Fin.val hpr
      omega)]

lemma qExt_qUpdate_of_gt {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (u : ℝ) {n : ℕ} (hn : r.val + 1 < n) :
    qExt (qUpdate qs r u) n = qExt qs n := by
  rcases n with _ | n
  · omega
  · by_cases hnlt : n < k + 1
    · let p : Fin (k + 1) := ⟨n, hnlt⟩
      rw [show n + 1 = p.val + 1 by rfl, qExt_qUpdate_succ]
      rw [if_neg (by
        intro hpr
        have : n = r.val := congrArg Fin.val hpr
        omega)]
    · rw [qExt_of_le (qUpdate qs r u) (by omega), qExt_of_le qs (by omega)]

lemma parisiVar_qUpdate_before {ξ : ℝ → ℝ} {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (u : ℝ) {n : ℕ} (hn : n < r.val) :
    parisiVar ξ (qUpdate qs r u) n = parisiVar ξ qs n := by
  unfold parisiVar
  rw [qExt_qUpdate_of_lt qs r u (by omega), qExt_qUpdate_of_lt qs r u (by omega)]

lemma parisiVar_qUpdate_after {ξ : ℝ → ℝ} {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (u : ℝ) {n : ℕ} (hn : r.val + 1 < n) :
    parisiVar ξ (qUpdate qs r u) n = parisiVar ξ qs n := by
  unfold parisiVar
  rw [qExt_qUpdate_of_gt qs r u (by omega), qExt_qUpdate_of_gt qs r u (by omega)]

lemma parisiVar_qUpdate_left {ξ : ℝ → ℝ} {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (u : ℝ) :
    parisiVar ξ (qUpdate qs r u) r.val =
      Real.toNNReal (deriv ξ u - deriv ξ (qExt qs r.val)) := by
  unfold parisiVar
  rw [qExt_qUpdate_self, qExt_qUpdate_of_lt qs r u (by omega)]

lemma parisiVar_qUpdate_right {ξ : ℝ → ℝ} {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (u : ℝ) :
    parisiVar ξ (qUpdate qs r u) (r.val + 1) =
      Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ u) := by
  unfold parisiVar
  rw [qExt_qUpdate_of_gt qs r u (by omega), qExt_qUpdate_self]

/-! ### Admissible parameters and minimization in the overlap variables -/

/-- The mass condition (14.103), with the endpoint values `m₀ = 0` and `m_{k+1} = 1`
supplied by `mExt`.  The formulation is also meaningful when `k = 0`. -/
def ParisiMAdmissible {k : ℕ} (ms : Fin k → ℝ) : Prop :=
  StrictMono ms ∧ (∀ i, 0 < ms i) ∧ ∀ i, ms i < 1

/-- The free-coordinate form of the overlap condition (14.104):
`0 ≤ q₁ < ⋯ < q_{k+1} ≤ 1`. -/
def ParisiQAdmissible {k : ℕ} (qs : Fin (k + 1) → ℝ) : Prop :=
  StrictMono qs ∧ 0 ≤ qs 0 ∧ qs (Fin.last k) ≤ 1

/-- A directly usable formulation of Talagrand's covariance hypotheses (14.101). The second
derivative is required to be positive away from zero, but it may vanish at zero. -/
structure TalagrandXiCondition (ξ : ℝ → ℝ) : Prop where
  even : Function.Even ξ
  convex : ConvexOn ℝ Set.univ ξ
  deriv_continuous : ContinuousOn (deriv ξ) (Icc (0 : ℝ) 1)
  hasDeriv : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt ξ (deriv ξ x) x
  hasDeriv_deriv : ∀ x ∈ Icc (0 : ℝ) 1,
    HasDerivAt (deriv ξ) (deriv (deriv ξ) x) x
  second_pos : ∀ x ∈ Icc (0 : ℝ) 1, x ≠ 0 → 0 < deriv (deriv ξ) x
  hasDeriv_second : ∀ x ∈ Ioc (0 : ℝ) 1,
    HasDerivAt (deriv (deriv ξ)) (deriv (deriv (deriv ξ)) x) x
  third_nonneg : ∀ x ∈ Ioc (0 : ℝ) 1, 0 ≤ deriv (deriv (deriv ξ)) x

lemma TalagrandXiCondition.strictMonoOn_deriv {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) : StrictMonoOn (deriv ξ) (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) hξ.deriv_continuous
  intro x hx
  apply hξ.second_pos x (interior_subset hx)
  have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
  exact ne_of_gt hx'.1

lemma TalagrandXiCondition.monotoneOn_second {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) : MonotoneOn (deriv (deriv ξ)) (Ioc (0 : ℝ) 1) := by
  have hc : ContinuousOn (deriv (deriv ξ)) (Ioc (0 : ℝ) 1) :=
    fun x hx => (hξ.hasDeriv_second x hx).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ (deriv (deriv ξ)) (interior (Ioc (0 : ℝ) 1)) := by
    rw [interior_Ioc]
    intro x hx
    exact (hξ.hasDeriv_second x ⟨hx.1, hx.2.le⟩).differentiableAt.differentiableWithinAt
  refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 1) hc hd ?_
  intro x hx
  rw [interior_Ioc] at hx
  rw [(hξ.hasDeriv_second x ⟨hx.1, hx.2.le⟩).deriv]
  exact hξ.third_nonneg x ⟨hx.1, hx.2.le⟩

/-- With the mass parameters fixed, no admissible overlap vector has a smaller value of the
Parisi functional.  In particular, coordinate variations are constrained by their neighboring
overlaps, as required by (14.104). -/
def IsParisiQMinimizer (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) : Prop :=
  ParisiQAdmissible qs ∧
    ∀ qs', ParisiQAdmissible qs' → parisiFunctional ξ h ms qs ≤ parisiFunctional ξ h ms qs'

lemma ParisiQAdmissible.monotone {k : ℕ} {qs : Fin (k + 1) → ℝ}
    (hq : ParisiQAdmissible qs) : Monotone qs :=
  hq.1.monotone

lemma ParisiQAdmissible.mem_Icc {k : ℕ} {qs : Fin (k + 1) → ℝ}
    (hq : ParisiQAdmissible qs) (r : Fin (k + 1)) : qs r ∈ Icc (0 : ℝ) 1 := by
  exact ⟨hq.2.1.trans (hq.1.monotone (Fin.zero_le r)),
    (hq.1.monotone (Fin.le_last r)).trans hq.2.2⟩

/-- Replacing one overlap by a value strictly between every overlap on its left and every overlap
on its right preserves (14.104). -/
lemma ParisiQAdmissible.qUpdate {k : ℕ} {qs : Fin (k + 1) → ℝ}
    (hq : ParisiQAdmissible qs) (r : Fin (k + 1)) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hleft : ∀ p, p < r → qs p < u) (hright : ∀ p, r < p → u < qs p) :
    ParisiQAdmissible (qUpdate qs r u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    by_cases har : a = r
    · subst a
      rw [qUpdate_self, qUpdate_of_ne qs u (ne_of_gt hab)]
      exact hright b hab
    · by_cases hbr : b = r
      · subst b
        rw [qUpdate_of_ne qs u har, qUpdate_self]
        exact hleft a hab
      · rw [qUpdate_of_ne qs u har, qUpdate_of_ne qs u hbr]
        exact hq.1 hab
  · by_cases hr0 : (0 : Fin (k + 1)) = r
    · rw [hr0, qUpdate_self]
      exact hu0
    · rw [qUpdate_of_ne qs u hr0]
      exact hq.2.1
  · by_cases hrlast : Fin.last k = r
    · rw [hrlast, qUpdate_self]
      exact hu1
    · rw [qUpdate_of_ne qs u hrlast]
      exact hq.2.2

/-- Admissible global minimization gives the correctly constrained one-coordinate comparison. -/
lemma IsParisiQMinimizer.le_qUpdate {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} {ms : Fin k → ℝ}
    {qs : Fin (k + 1) → ℝ} (hmin : IsParisiQMinimizer ξ h ms qs) (r : Fin (k + 1)) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hleft : ∀ p, p < r → qs p < u) (hright : ∀ p, r < p → u < qs p) :
    parisiFunctional ξ h ms qs ≤ parisiFunctional ξ h ms (qUpdate qs r u) :=
  hmin.2 _ (hmin.1.qUpdate r hu0 hu1 hleft hright)

lemma parisiQMin_isLocalMin {k : ℕ} {qs : Fin (k + 1) → ℝ}
    {F : (Fin (k + 1) → ℝ) → ℝ}
    (hmin : ParisiQAdmissible qs ∧ ∀ qs', ParisiQAdmissible qs' → F qs ≤ F qs')
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) (r : Fin (k + 1)) :
    IsLocalMin (fun u => F (qUpdate qs r u)) (qs r) := by
  have hu0 : ∀ᶠ u in nhds (qs r), 0 ≤ u :=
    eventually_ge_nhds (hq0.trans_le (hmin.1.monotone (Fin.zero_le r)))
  have hu1 : ∀ᶠ u in nhds (qs r), u ≤ 1 :=
    eventually_le_nhds ((hmin.1.monotone (Fin.le_last r)).trans_lt hq1)
  have hleft : ∀ᶠ u in nhds (qs r), ∀ p : Fin (k + 1), p < r → qs p < u := by
    exact Filter.eventually_all.2 (fun p => by
      by_cases hp : p < r
      · filter_upwards [eventually_gt_nhds (hmin.1.1 hp)] with u hu
        exact fun _ => hu
      · exact Filter.Eventually.of_forall fun _ hpr => (hp hpr).elim)
  have hright : ∀ᶠ u in nhds (qs r), ∀ p : Fin (k + 1), r < p → u < qs p := by
    exact Filter.eventually_all.2 (fun p => by
      by_cases hp : r < p
      · filter_upwards [eventually_lt_nhds (hmin.1.1 hp)] with u hu
        exact fun _ => hu
      · exact Filter.Eventually.of_forall fun _ hrp => (hp hrp).elim)
  have hle : ∀ᶠ u in nhds (qs r),
      F qs ≤ F (qUpdate qs r u) := by
    filter_upwards [hu0, hu1, hleft, hright] with u hu0 hu1 hleft hright
    exact hmin.2 _ (hmin.1.qUpdate r hu0 hu1 hleft hright)
  change ∀ᶠ u in nhds (qs r),
    F (qUpdate qs r (qs r)) ≤
      F (qUpdate qs r u)
  simpa [qUpdate] using hle

lemma parisiQMin_first_deriv_nonneg {k : ℕ} {qs : Fin (k + 1) → ℝ}
    {F : (Fin (k + 1) → ℝ) → ℝ}
    (hmin : ParisiQAdmissible qs ∧ ∀ qs', ParisiQAdmissible qs' → F qs ≤ F qs')
    (hq0 : qs 0 = 0) {d : ℝ}
    (hd : HasDerivAt (fun u => F (qUpdate qs 0 u)) d (qs 0)) : 0 ≤ d := by
  have hq1 : qs 0 < 1 := by rw [hq0]; norm_num
  have hadm : ∀ᶠ u in nhdsWithin (qs 0) (Ici (qs 0)),
      ParisiQAdmissible (qUpdate qs 0 u) := by
    have hu0 : ∀ᶠ u in nhdsWithin (qs 0) (Ici (qs 0)), 0 ≤ u := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact hq0 ▸ hu
    have hu1 : ∀ᶠ u in nhdsWithin (qs 0) (Ici (qs 0)), u ≤ 1 :=
      (eventually_le_nhds hq1).filter_mono inf_le_left
    have hright : ∀ᶠ u in nhdsWithin (qs 0) (Ici (qs 0)),
        ∀ p : Fin (k + 1), 0 < p → u < qs p := by
      exact Filter.eventually_all.2 (fun p => by
        by_cases hp : (0 : Fin (k + 1)) < p
        · exact (eventually_lt_nhds (hmin.1.1 hp)).filter_mono inf_le_left |>.mono
            fun _ hu _ => hu
        · exact Filter.Eventually.of_forall fun _ hp' => (hp hp').elim)
    filter_upwards [hu0, hu1, hright] with u hu0 hu1 hright
    exact hmin.1.qUpdate 0 hu0 hu1 (fun p hp => (Fin.not_lt_zero p hp).elim) hright
  have hlocal : IsLocalMinOn (fun u => F (qUpdate qs 0 u))
      (Ici (qs 0)) (qs 0) := by
    filter_upwards [hadm] with u hu
    simpa [qUpdate] using hmin.2 _ hu
  have htangent : (1 : ℝ) ∈ posTangentConeAt (Ici (qs 0)) (qs 0) := by
    convert sub_mem_posTangentConeAt_of_segment_subset
      (s := Ici (qs 0)) (x := qs 0) (y := qs 0 + 1) (by
        rw [segment_eq_Icc (by linarith : qs 0 ≤ qs 0 + 1)]
        exact Icc_subset_Ici_self) using 1
    ring
  have hd_nonneg := hlocal.hasFDerivWithinAt_nonneg
    hd.hasFDerivAt.hasFDerivWithinAt htangent
  change 0 ≤ (1 : ℝ) * d at hd_nonneg
  simpa using hd_nonneg

lemma parisiQMin_last_derivWithin_nonpos {k : ℕ} {qs : Fin (k + 1) → ℝ}
    {F : (Fin (k + 1) → ℝ) → ℝ}
    (hmin : ParisiQAdmissible qs ∧ ∀ qs', ParisiQAdmissible qs' → F qs ≤ F qs')
    (hq1 : qs (Fin.last k) = 1) {d : ℝ}
    (hd : HasDerivWithinAt (fun u => F (qUpdate qs (Fin.last k) u)) d
      (Iic (qs (Fin.last k))) (qs (Fin.last k))) : d ≤ 0 := by
  have hq0 : 0 < qs (Fin.last k) := by rw [hq1]; norm_num
  have hadm : ∀ᶠ u in nhdsWithin (qs (Fin.last k)) (Iic (qs (Fin.last k))),
      ParisiQAdmissible (qUpdate qs (Fin.last k) u) := by
    have hu0 : ∀ᶠ u in nhdsWithin (qs (Fin.last k)) (Iic (qs (Fin.last k))), 0 ≤ u :=
      (eventually_ge_nhds hq0).filter_mono inf_le_left
    have hu1 : ∀ᶠ u in nhdsWithin (qs (Fin.last k)) (Iic (qs (Fin.last k))), u ≤ 1 := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact hq1 ▸ hu
    have hleft : ∀ᶠ u in nhdsWithin (qs (Fin.last k)) (Iic (qs (Fin.last k))),
        ∀ p : Fin (k + 1), p < Fin.last k → qs p < u := by
      exact Filter.eventually_all.2 (fun p => by
        by_cases hp : p < Fin.last k
        · exact (eventually_gt_nhds (hmin.1.1 hp)).filter_mono inf_le_left |>.mono
            fun _ hu _ => hu
        · exact Filter.Eventually.of_forall fun _ hp' => (hp hp').elim)
    filter_upwards [hu0, hu1, hleft] with u hu0 hu1 hleft
    exact hmin.1.qUpdate (Fin.last k) hu0 hu1 hleft
      (fun p hp => (not_lt_of_ge (Fin.le_last p) hp).elim)
  have hlocal : IsLocalMinOn
      (fun u => F (qUpdate qs (Fin.last k) u))
      (Iic (qs (Fin.last k))) (qs (Fin.last k)) := by
    filter_upwards [hadm] with u hu
    simpa [qUpdate] using hmin.2 _ hu
  have htangent : (-1 : ℝ) ∈
      posTangentConeAt (Iic (qs (Fin.last k))) (qs (Fin.last k)) := by
    convert sub_mem_posTangentConeAt_of_segment_subset
      (s := Iic (qs (Fin.last k))) (x := qs (Fin.last k))
      (y := qs (Fin.last k) - 1) (by
        rw [segment_symm, segment_eq_Icc
          (by linarith : qs (Fin.last k) - 1 ≤ qs (Fin.last k))]
        exact Icc_subset_Iic_self) using 1
    ring
  have hd_nonneg := hlocal.hasFDerivWithinAt_nonneg
    hd.hasFDerivWithinAt htangent
  change 0 ≤ (-1 : ℝ) * d at hd_nonneg
  linarith

/-- If both endpoint inequalities are strict, admissible global minimality gives an ordinary
local minimum along every overlap coordinate. -/
lemma IsParisiQMinimizer.isLocalMin_qUpdate
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hmin : IsParisiQMinimizer ξ h ms qs) (hq0 : 0 < qs 0)
    (hq1 : qs (Fin.last k) < 1) (r : Fin (k + 1)) :
    IsLocalMin (fun u => parisiFunctional ξ h ms (qUpdate qs r u)) (qs r) :=
  parisiQMin_isLocalMin hmin hq0 hq1 r

/-- At the lower endpoint, constrained minimality forces a nonnegative right derivative. -/
lemma IsParisiQMinimizer.first_deriv_nonneg
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ}
    (hmin : IsParisiQMinimizer ξ h ms qs) (hq0 : qs 0 = 0) {d : ℝ}
    (hd : HasDerivAt (fun u => parisiFunctional ξ h ms (qUpdate qs 0 u)) d (qs 0)) :
    0 ≤ d :=
  parisiQMin_first_deriv_nonneg hmin hq0 hd

/-- At the upper endpoint, constrained minimality forces a nonpositive left derivative. -/
lemma IsParisiQMinimizer.last_deriv_nonpos
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ}
    (hmin : IsParisiQMinimizer ξ h ms qs) (hq1 : qs (Fin.last k) = 1) {d : ℝ}
    (hd : HasDerivAt
      (fun u => parisiFunctional ξ h ms (qUpdate qs (Fin.last k) u)) d
      (qs (Fin.last k))) : d ≤ 0 :=
  parisiQMin_last_derivWithin_nonpos hmin hq1 hd.hasDerivWithinAt

/-- Every consecutive mass gap is positive under (14.103), including the first and last gaps
and the vacuous-mass case `k = 0`. -/
lemma ParisiMAdmissible.mExt_gap_pos {k : ℕ} {ms : Fin k → ℝ}
    (hm : ParisiMAdmissible ms) (r : Fin (k + 1)) :
    0 < mExt ms (r.val + 1) - mExt ms r.val := by
  have hrle : r.val ≤ k := by omega
  by_cases htop : r.val = k
  · by_cases hk : k = 0
    · subst k
      have hr : r.val = 0 := by omega
      rw [hr, mExt_zero, mExt_of_zero_lt (r := 1) (by omega)]
      norm_num
    · let p : Fin k := ⟨k - 1, by omega⟩
      have hr : r.val = p.val + 1 := by simp [p]; omega
      have hu : mExt ms (r.val + 1) = 1 :=
        mExt_eq_one_of_le ms (by omega)
      have hl : mExt ms r.val = ms p := by
        rw [hr, mExt_val_succ]
      rw [hu, hl]
      linarith [hm.2.2 p]
  · have hrlt : r.val < k := lt_of_le_of_ne hrle htop
    let p : Fin k := ⟨r.val, hrlt⟩
    have hu : mExt ms (r.val + 1) = ms p := by
      simpa [p] using mExt_val_succ ms p
    rw [hu]
    by_cases hr0 : r.val = 0
    · rw [hr0, mExt_zero]
      simpa using hm.2.1 p
    · let p' : Fin k := ⟨r.val - 1, by omega⟩
      have hl : mExt ms r.val = ms p' := by
        have hv : r.val = p'.val + 1 := by simp [p']; omega
        rw [hv, mExt_val_succ]
      rw [hl]
      apply sub_pos.mpr
      apply hm.1
      apply Fin.mk_lt_mk.mpr
      omega

/-- Every positive extended mass index has positive mass under (14.103). -/
lemma ParisiMAdmissible.mExt_pos {k : ℕ} {ms : Fin k → ℝ}
    (hm : ParisiMAdmissible ms) {n : ℕ} (hn : 0 < n) : 0 < mExt ms n := by
  by_cases hnk : n ≤ k
  · let p : Fin k := ⟨n - 1, by omega⟩
    have hn_eq : n = p.val + 1 := by simp [p]; omega
    rw [hn_eq, mExt_val_succ]
    exact hm.2.1 p
  · rw [mExt_eq_one_of_le ms (by omega)]
    norm_num


end

end SpinGlass
