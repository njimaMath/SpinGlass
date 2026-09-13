/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.ParisiFunctional
import Common.Mathlib.Probability.PointProcess.CascadeColeHopf
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Derivatives of the Parisi functional in the overlap coordinates

This file specializes the variance-split derivative for the Cole--Hopf operators to the
overlap coordinates of the Parisi functional, following Talagrand, Vol. II, Section 14.7.  It
also records the admissible parameter spaces in (14.103)--(14.104) and the corresponding notion
of minimization with the mass parameters fixed.

## Main definitions

* `coleHopfSplitMoment`: the moment in the right-hand side of (14.219).
* `qUpdate`: replacement of one free overlap coordinate.
* `parisiQConst`: the part of the theta sum independent of that coordinate.
* `ParisiMAdmissible`, `ParisiQAdmissible`: the conditions (14.103) and (14.104).
* `IsParisiQMinimizer`: the statement that no admissible change of the overlap vector decreases
  the Parisi functional.

## Main results

* `hasDerivAt_coleHopf_coleHopf_q`: the local derivative (14.219).
* `hasDerivAt_parisiFunctional_qUpdate`: the derivative of the Parisi functional (14.220).
* `parisiQ_eq_moment_of_isLocalMin`: the stationarity equation (14.222).
* `parisiQ_strict_chain_and_eq_moment_of_isMin`: Proposition 14.7.5, including (14.221) and
  (14.222).
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

/-! ### The local two-level derivative: (14.219) -/

/-- The expectation in the right hand side of Talagrand's (14.219).

Here `vR = ξ'(q_{r+1}) - ξ'(q_r)` is the variance of the inner level and
`vL = ξ'(q_r) - ξ'(q_{r-1})` is the variance of the outer level. The inner integral is
`A_r'`, written in the `coleHopfQ` normal form supplied by the Cole--Hopf API, and the outer
`coleHopfQ` is Talagrand's weight `W_{r-1}`. -/
noncomputable def coleHopfSplitMoment (m m' : ℝ) (vR vL : ℝ≥0)
    (A A' : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, (∫ w, A' (x + z + w) * coleHopfQ m vR A (x + z) w ∂gaussianReal 0 vR) ^ 2
      * coleHopfQ m' vL (coleHopf m vR A) x z ∂gaussianReal 0 vL

/-- Talagrand's (14.219).

With
`A_r = T_{m, ξ'(qR)-ξ'(q)} A` and
`A_{r-1} = T_{m', ξ'(q)-ξ'(qL)} A_r`, the derivative with respect to the middle overlap is

`-(1 / 2) ξ''(q) (m - m') E[A_r'(x + z)^2 W_{r-1}]`.

The proof is only the chain rule applied to
`ProbabilityTheory.hasDerivAt_coleHopf_coleHopf_var` (Lemma 14.7.3 / (14.207)). -/
theorem hasDerivAt_coleHopf_coleHopf_q
    {ξ : ℝ → ℝ} {ξ₂ qL q qR m m' : ℝ} {A A' A'' : ℝ → ℝ}
    (hA : ∀ y, HasDerivAt A (A' y) y)
    (hA' : ∀ y, HasDerivAt A' (A'' y) y)
    (hA''c : Continuous A'') {L L₂ : ℝ}
    (hL : ∀ y, |A' y| ≤ L) (hL₂ : ∀ y, |A'' y| ≤ L₂)
    (hm : m ≠ 0) (hξ₂ : HasDerivAt (deriv ξ) ξ₂ q)
    (hleft : deriv ξ qL < deriv ξ q) (hright : deriv ξ q < deriv ξ qR)
    (x : ℝ) :
    HasDerivAt
      (fun u => coleHopf m' (Real.toNNReal (deriv ξ u - deriv ξ qL))
        (coleHopf m (Real.toNNReal (deriv ξ qR - deriv ξ u)) A) x)
      ((-1 / 2 : ℝ) * ξ₂ * (m - m') *
        coleHopfSplitMoment m m'
          (Real.toNNReal (deriv ξ qR - deriv ξ q))
          (Real.toNNReal (deriv ξ q - deriv ξ qL)) A A' x)
      q := by
  let a : ℝ := deriv ξ qR - deriv ξ qL
  let v : ℝ → ℝ := fun u => deriv ξ qR - deriv ξ u
  have hv : HasDerivAt v (-ξ₂) q := by
    dsimp [v]
    simpa using hξ₂.const_sub (deriv ξ qR)
  have hvpos : 0 < v q := by
    dsimp [v]
    linarith
  have hva : v q < a := by
    dsimp [v, a]
    linarith
  have hs := ProbabilityTheory.hasDerivAt_coleHopf_coleHopf_var
    (m := m) (m' := m') (a := a) (v₀ := v q)
    hA hA' hA''c hL hL₂ hm hvpos hva x
  have hc := hs.comp q hv
  have hav : ∀ u, a - v u = deriv ξ u - deriv ξ qL := by
    intro u
    dsimp [a, v]
    ring
  have hfun :
      (fun u => coleHopf m' (Real.toNNReal (deriv ξ u - deriv ξ qL))
        (coleHopf m (Real.toNNReal (deriv ξ qR - deriv ξ u)) A) x)
        = (fun u => coleHopf m' (Real.toNNReal (a - v u))
          (coleHopf m (Real.toNNReal (v u)) A) x) := by
    funext u
    rw [hav u]
  rw [hfun]
  refine hc.congr_deriv ?_
  unfold coleHopfSplitMoment
  rw [hav q]
  dsimp [v]
  ring

/-- The propagated form of (14.219), after the earlier positive-exponent levels and the outer
Gaussian `z₀` average. This is the direct `q`-coordinate specialization of
`hasDerivAt_integral_coleHopfIterate_split`; its integral is Talagrand's
`E(W₁ ⋯ W_{r-1} A_r'(ζ_r)^2)` with the factor `(m_r - m_{r-1}) / 2` still inside the integral. -/
theorem hasDerivAt_integral_coleHopfIterate_q
    {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    {ξ : ℝ → ℝ} {ξ₂ qL q qR m m' : ℝ} {A A' A'' : ℝ → ℝ}
    (hA : ∀ y, HasDerivAt A (A' y) y)
    (hA' : ∀ y, HasDerivAt A' (A'' y) y)
    (hA''c : Continuous A'') {L L₂ : ℝ}
    (hL : ∀ y, |A' y| ≤ L) (hL₂ : ∀ y, |A'' y| ≤ L₂)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hm : m ≠ 0) (hξ₂ : HasDerivAt (deriv ξ) ξ₂ q)
    (hleft : deriv ξ qL < deriv ξ q) (hright : deriv ξ q < deriv ξ qR)
    (w₀ : ℝ≥0) (h : ℝ) :
    HasDerivAt
      (fun u => ∫ z₀, coleHopfIterate j ms vs
        (fun y => coleHopf m' (Real.toNNReal (deriv ξ u - deriv ξ qL))
          (coleHopf m (Real.toNNReal (deriv ξ qR - deriv ξ u)) A) y)
        (h + z₀) ∂gaussianReal 0 w₀)
      ((∫ z₀, ∫ zs, ((m - m') / 2) * ∫ z,
          (∫ w, A' (h + z₀ + ∑ p, zs p + z + w)
              * coleHopfQ m (Real.toNNReal (deriv ξ qR - deriv ξ q)) A
                  (h + z₀ + ∑ p, zs p + z) w
                ∂gaussianReal 0 (Real.toNNReal (deriv ξ qR - deriv ξ q))) ^ 2
            * coleHopfQ m' (Real.toNNReal (deriv ξ q - deriv ξ qL))
                (coleHopf m (Real.toNNReal (deriv ξ qR - deriv ξ q)) A)
                (h + z₀ + ∑ p, zs p) z
              ∂gaussianReal 0 (Real.toNNReal (deriv ξ q - deriv ξ qL))
          ∂cascadeTiltMeasure j ms (fun p => gaussianReal 0 (vs p))
            (fun zs => ENNReal.ofReal (Real.exp
              (coleHopf m' (Real.toNNReal (deriv ξ q - deriv ξ qL))
                (coleHopf m (Real.toNNReal (deriv ξ qR - deriv ξ q)) A)
                (h + z₀ + ∑ p, zs p))))
        ∂gaussianReal 0 w₀) * (-ξ₂)) q := by
  let a : ℝ := deriv ξ qR - deriv ξ qL
  let v : ℝ → ℝ := fun u => deriv ξ qR - deriv ξ u
  have hv : HasDerivAt v (-ξ₂) q := by
    dsimp [v]
    simpa using hξ₂.const_sub (deriv ξ qR)
  have hvpos : 0 < v q := by
    dsimp [v]
    linarith
  have hva : v q < a := by
    dsimp [v, a]
    linarith
  have hs := ProbabilityTheory.hasDerivAt_integral_coleHopfIterate_split
    (m := m) (m' := m') (a := a) (v₀ := v q)
    ms vs hA hA' hA''c hL hL₂ hpos hle hm hvpos hva w₀ h
  have hc := hs.comp q hv
  have hav : ∀ u, a - v u = deriv ξ u - deriv ξ qL := by
    intro u
    dsimp [a, v]
    ring
  have hfun :
      (fun u => ∫ z₀, coleHopfIterate j ms vs
        (fun y => coleHopf m' (Real.toNNReal (deriv ξ u - deriv ξ qL))
          (coleHopf m (Real.toNNReal (deriv ξ qR - deriv ξ u)) A) y)
        (h + z₀) ∂gaussianReal 0 w₀)
        = (fun u => ∫ z₀, coleHopfIterate j ms vs
          (fun y => coleHopf m' (Real.toNNReal (a - v u))
            (coleHopf m (Real.toNNReal (v u)) A) y)
          (h + z₀) ∂gaussianReal 0 w₀) := by
    funext u
    rw [hav u]
  rw [hfun]
  refine hc.congr_deriv ?_
  rw [hav q]

/-! ### The `q_r`-dependent part of the Parisi functional -/

/-- Replace one free overlap coordinate. A `Fin (k + 1)` index `r` represents Talagrand's
coordinate `q_{r+1}`. -/
def qUpdate {k : ℕ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : ℝ) :
    Fin (k + 1) → ℝ :=
  Function.update qs r u

@[simp] lemma qUpdate_self {k : ℕ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : ℝ) :
    qUpdate qs r u r = u := by
  simp [qUpdate]

@[simp] lemma qUpdate_of_ne {k : ℕ} (qs : Fin (k + 1) → ℝ) {r p : Fin (k + 1)} (u : ℝ)
    (hpr : p ≠ r) : qUpdate qs r u p = qs p := by
  simp [qUpdate, hpr]

/-! ### Admissible parameters and minimization in the overlap variables -/

/-- The mass condition (14.103), with the endpoint values `m₀ = 0` and `m_{k+1} = 1`
supplied by `mExt`.  The formulation is also meaningful when `k = 0`. -/
def ParisiMAdmissible {k : ℕ} (ms : Fin k → ℝ) : Prop :=
  StrictMono ms ∧ (∀ i, 0 < ms i) ∧ ∀ i, ms i < 1

/-- The free-coordinate form of the overlap condition (14.104):
`0 ≤ q₁ < ⋯ < q_{k+1} ≤ 1`. -/
def ParisiQAdmissible {k : ℕ} (qs : Fin (k + 1) → ℝ) : Prop :=
  StrictMono qs ∧ 0 ≤ qs 0 ∧ qs (Fin.last k) ≤ 1

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

/-- If both endpoint inequalities are strict, admissible global minimality gives an ordinary
local minimum along every overlap coordinate. -/
lemma IsParisiQMinimizer.isLocalMin_qUpdate
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hmin : IsParisiQMinimizer ξ h ms qs) (hq0 : 0 < qs 0)
    (hq1 : qs (Fin.last k) < 1) (r : Fin (k + 1)) :
    IsLocalMin (fun u => parisiFunctional ξ h ms (qUpdate qs r u)) (qs r) := by
  have hu0 : ∀ᶠ u in nhds (qs r), 0 ≤ u :=
    eventually_ge_nhds (hq0.trans_le (hmin.1.monotone (Fin.zero_le r)))
  have hu1 : ∀ᶠ u in nhds (qs r), u ≤ 1 :=
    eventually_le_nhds ((hmin.1.monotone (Fin.le_last r)).trans_lt hq1)
  have hleft : ∀ᶠ u in nhds (qs r), ∀ p : Fin (k + 1), p < r → qs p < u := by
    have hall : ∀ᶠ u in nhds (qs r), ∀ p ∈ Finset.univ, p < r → qs p < u :=
      (Filter.eventually_all_finset Finset.univ).2 (fun p _ => by
        by_cases hp : p < r
        · filter_upwards [eventually_gt_nhds (hmin.1.1 hp)] with u hu
          exact fun _ => hu
        · exact Filter.Eventually.of_forall fun _ hpr => (hp hpr).elim)
    simpa using hall
  have hright : ∀ᶠ u in nhds (qs r), ∀ p : Fin (k + 1), r < p → u < qs p := by
    have hall : ∀ᶠ u in nhds (qs r), ∀ p ∈ Finset.univ, r < p → u < qs p :=
      (Filter.eventually_all_finset Finset.univ).2 (fun p _ => by
        by_cases hp : r < p
        · filter_upwards [eventually_lt_nhds (hmin.1.1 hp)] with u hu
          exact fun _ => hu
        · exact Filter.Eventually.of_forall fun _ hrp => (hp hrp).elim)
    simpa using hall
  have hle : ∀ᶠ u in nhds (qs r),
      parisiFunctional ξ h ms qs ≤ parisiFunctional ξ h ms (qUpdate qs r u) := by
    filter_upwards [hu0, hu1, hleft, hright] with u hu0 hu1 hleft hright
    exact hmin.le_qUpdate r hu0 hu1 hleft hright
  change ∀ᶠ u in nhds (qs r),
    parisiFunctional ξ h ms (qUpdate qs r (qs r)) ≤
      parisiFunctional ξ h ms (qUpdate qs r u)
  simpa [qUpdate] using hle

/-- At the lower endpoint, constrained minimality forces a nonnegative right derivative. -/
lemma IsParisiQMinimizer.first_deriv_nonneg
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ}
    (hmin : IsParisiQMinimizer ξ h ms qs) (hq0 : qs 0 = 0) {d : ℝ}
    (hd : HasDerivAt (fun u => parisiFunctional ξ h ms (qUpdate qs 0 u)) d (qs 0)) :
    0 ≤ d := by
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
      have hall : ∀ᶠ u in nhdsWithin (qs 0) (Ici (qs 0)), ∀ p ∈ Finset.univ,
          (0 : Fin (k + 1)) < p → u < qs p :=
        (Filter.eventually_all_finset Finset.univ).2 (fun p _ => by
          by_cases hp : (0 : Fin (k + 1)) < p
          · exact (eventually_lt_nhds (hmin.1.1 hp)).filter_mono inf_le_left |>.mono
              fun _ hu _ => hu
          · exact Filter.Eventually.of_forall fun _ hp' => (hp hp').elim)
      simpa using hall
    filter_upwards [hu0, hu1, hright] with u hu0 hu1 hright
    exact hmin.1.qUpdate 0 hu0 hu1 (fun p hp => (Fin.not_lt_zero p hp).elim) hright
  have hlocal : IsLocalMinOn (fun u => parisiFunctional ξ h ms (qUpdate qs 0 u))
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

/-- At the upper endpoint, constrained minimality forces a nonpositive left derivative. -/
lemma IsParisiQMinimizer.last_deriv_nonpos
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ}
    (hmin : IsParisiQMinimizer ξ h ms qs) (hq1 : qs (Fin.last k) = 1) {d : ℝ}
    (hd : HasDerivAt
      (fun u => parisiFunctional ξ h ms (qUpdate qs (Fin.last k) u)) d
      (qs (Fin.last k))) : d ≤ 0 := by
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
      have hall : ∀ᶠ u in nhdsWithin (qs (Fin.last k)) (Iic (qs (Fin.last k))),
          ∀ p ∈ Finset.univ, p < Fin.last k → qs p < u :=
        (Filter.eventually_all_finset Finset.univ).2 (fun p _ => by
          by_cases hp : p < Fin.last k
          · exact (eventually_gt_nhds (hmin.1.1 hp)).filter_mono inf_le_left |>.mono
              fun _ hu _ => hu
          · exact Filter.Eventually.of_forall fun _ hp' => (hp hp').elim)
      simpa using hall
    filter_upwards [hu0, hu1, hleft] with u hu0 hu1 hleft
    exact hmin.1.qUpdate (Fin.last k) hu0 hu1 hleft
      (fun p hp => (not_lt_of_ge (Fin.le_last p) hp).elim)
  have hlocal : IsLocalMinOn
      (fun u => parisiFunctional ξ h ms (qUpdate qs (Fin.last k) u))
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
    hd.hasFDerivAt.hasFDerivWithinAt htangent
  change 0 ≤ (-1 : ℝ) * d at hd_nonneg
  linarith

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

/-- The theta-sum form of the Parisi functional, indexed by `Fin (k + 1)` rather than naturals. -/
theorem parisiFunctional_eq_theta_fin_sum (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    parisiFunctional ξ h ms qs
      = Real.log 2 + parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x)))
        + (1 / 2) * ∑ p : Fin (k + 1),
            parisiTheta ξ (qs p) * (mExt ms (p.val + 1) - mExt ms p.val)
        - (1 / 2) * parisiTheta ξ 1 := by
  rw [parisiFunctional_eq_theta_sum]
  have hsum :
      (∑ p ∈ Finset.range (k + 1),
          parisiTheta ξ (qExt qs (p + 1)) * (mExt ms (p + 1) - mExt ms p))
        = ∑ p : Fin (k + 1),
            parisiTheta ξ (qs p) * (mExt ms (p.val + 1) - mExt ms p.val) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [qExt_succ_of_lt qs p.isLt]
  rw [hsum]

/-- The part of the theta-sum independent of the coordinate `q_{r+1}`. -/
noncomputable def parisiQConst (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) : ℝ :=
  Real.log 2
    + (1 / 2) * ∑ p ∈ Finset.univ.erase r,
        parisiTheta ξ (qs p) * (mExt ms (p.val + 1) - mExt ms p.val)
    - (1 / 2) * parisiTheta ξ 1

/-- Along one overlap coordinate, the full Parisi functional is a constant plus `X₀(q)` plus
`(1 / 2) (m_r - m_{r-1}) θ(q)`. This is the form used in passing from the derivative of `X₀` to
(14.220). -/
theorem parisiFunctional_qUpdate_eq (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : ℝ) :
    parisiFunctional ξ h ms (qUpdate qs r u)
      = parisiQConst ξ ms qs r
        + (parisiX₀ ξ ms (qUpdate qs r u) (fun x => Real.log (Real.cosh (h + x)))
          + (1 / 2) * (mExt ms (r.val + 1) - mExt ms r.val) * parisiTheta ξ u) := by
  classical
  rw [parisiFunctional_eq_theta_fin_sum]
  have hsum :
      (∑ p : Fin (k + 1),
          parisiTheta ξ (qUpdate qs r u p) * (mExt ms (p.val + 1) - mExt ms p.val))
        = (∑ p ∈ Finset.univ.erase r,
            parisiTheta ξ (qs p) * (mExt ms (p.val + 1) - mExt ms p.val))
          + parisiTheta ξ u * (mExt ms (r.val + 1) - mExt ms r.val) := by
    calc
      (∑ p : Fin (k + 1),
          parisiTheta ξ (qUpdate qs r u p) * (mExt ms (p.val + 1) - mExt ms p.val))
          = (∑ p ∈ Finset.univ.erase r,
              parisiTheta ξ (qUpdate qs r u p) * (mExt ms (p.val + 1) - mExt ms p.val))
            + parisiTheta ξ (qUpdate qs r u r)
                * (mExt ms (r.val + 1) - mExt ms r.val) := by
          rw [Finset.sum_erase_add _ _ (Finset.mem_univ r)]
      _ = (∑ p ∈ Finset.univ.erase r,
              parisiTheta ξ (qs p) * (mExt ms (p.val + 1) - mExt ms p.val))
            + parisiTheta ξ u * (mExt ms (r.val + 1) - mExt ms r.val) := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro p hp
            rw [qUpdate_of_ne qs u (Finset.ne_of_mem_erase hp)]
          · rw [qUpdate_self]
  rw [hsum]
  unfold parisiQConst
  ring

/-- `θ'(q) = q ξ''(q)`. -/
theorem hasDerivAt_parisiTheta {ξ : ℝ → ℝ} {q ξ₂ : ℝ}
    (hξ : HasDerivAt ξ (deriv ξ q) q)
    (hξ' : HasDerivAt (deriv ξ) ξ₂ q) :
    HasDerivAt (parisiTheta ξ) (q * ξ₂) q := by
  unfold parisiTheta
  have hfun : id * deriv ξ - ξ = fun x => x * deriv ξ x - ξ x := by
    rfl
  rw [← hfun]
  simpa only [id_eq, one_mul, mul_one, add_sub_cancel_left] using
    ((hasDerivAt_id q).mul hξ').sub hξ

/-- Talagrand's (14.220).

Assume the `q_{r+1}`-derivative of `X₀` has already been propagated through the preceding
Cole--Hopf levels, so that its derivative is
`-(1 / 2) ξ''(q) (m_r - m_{r-1}) M`. Then the derivative of the actual Parisi functional along
that coordinate is

`(1 / 2) (m_r - m_{r-1}) ξ''(q) (-M + q)`.

For Talagrand's application, `M = E(W₁ ⋯ W_{r-1} A_r'(ζ_r)^2)`; the propagation of (14.219)
through the earlier levels is exactly `hasDerivAt_coleHopfIterate_split` /
`hasDerivAt_integral_coleHopfIterate_split`. -/
theorem hasDerivAt_parisiFunctional_qUpdate
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) {q ξ₂ M : ℝ}
    (hX₀ : HasDerivAt
      (fun u => parisiX₀ ξ ms (qUpdate qs r u) (fun x => Real.log (Real.cosh (h + x))))
      ((-1 / 2 : ℝ) * ξ₂ * (mExt ms (r.val + 1) - mExt ms r.val) * M) q)
    (hξ : HasDerivAt ξ (deriv ξ q) q)
    (hξ' : HasDerivAt (deriv ξ) ξ₂ q) :
    HasDerivAt (fun u => parisiFunctional ξ h ms (qUpdate qs r u))
      ((1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) * ξ₂ * (-M + q)) q := by
  let C : ℝ := parisiQConst ξ ms qs r
  let c : ℝ := (1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val)
  have hθ := hasDerivAt_parisiTheta hξ hξ'
  have hbase := hX₀.add (hθ.const_mul c)
  have hall := (hasDerivAt_const q C).add hbase
  have hfun :
      (fun u => parisiFunctional ξ h ms (qUpdate qs r u))
        = (fun u => C +
          (parisiX₀ ξ ms (qUpdate qs r u) (fun x => Real.log (Real.cosh (h + x)))
            + c * parisiTheta ξ u)) := by
    funext u
    rw [parisiFunctional_qUpdate_eq]
  rw [hfun]
  refine hall.congr_deriv ?_
  dsimp [c]
  ring

/-! ### The strict overlap chain: (14.221) -/

/-- The strict chain form of Talagrand's (14.221): if the free `q`-coordinates are strictly
increasing and the two endpoints are strict, then every adjacent pair of the extended sequence
`q₀ = 0, q₁, …, q_{k+1}, q_{k+2} = 1` is strictly increasing. -/
theorem qExt_strict_succ {k : ℕ} {qs : Fin (k + 1) → ℝ}
    (hsm : StrictMono qs) (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1)
    {r : ℕ} (hr : r ≤ k + 1) : qExt qs r < qExt qs (r + 1) := by
  rcases r with _ | r
  · rw [qExt_zero, qExt_succ_of_lt qs (Nat.succ_pos k)]
    exact hq0
  · have hrk : r ≤ k := by omega
    rcases lt_or_eq_of_le hrk with hrlt | hrEq
    · rw [qExt_succ_of_lt qs (by omega : r < k + 1),
          qExt_succ_of_lt qs (by omega : r + 1 < k + 1)]
      apply hsm
      simp
    · rw [qExt_succ_of_lt qs (by omega : r < k + 1),
        qExt_of_le qs (by omega : k + 2 ≤ r + 2)]
      have hlast : (⟨r, by omega⟩ : Fin (k + 1)) = Fin.last k := by
        apply Fin.ext
        exact hrEq
      simpa only [hlast] using hq1

/-! ### The stationarity equation: (14.222) -/

/-- The stationary-point implication in Proposition 14.7.5, i.e. (14.222).

At an interior coordinatewise minimum, (14.220) has derivative zero.  If
`m_r - m_{r-1}` and `ξ''(q_r)` are nonzero, this forces `q_r = M`. -/
theorem parisiQ_eq_moment_of_isLocalMin
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) {q ξ₂ M : ℝ}
    (hmin : IsLocalMin (fun u => parisiFunctional ξ h ms (qUpdate qs r u)) q)
    (hX₀ : HasDerivAt
      (fun u => parisiX₀ ξ ms (qUpdate qs r u) (fun x => Real.log (Real.cosh (h + x))))
      ((-1 / 2 : ℝ) * ξ₂ * (mExt ms (r.val + 1) - mExt ms r.val) * M) q)
    (hξ : HasDerivAt ξ (deriv ξ q) q)
    (hξ' : HasDerivAt (deriv ξ) ξ₂ q)
    (hm : mExt ms (r.val + 1) ≠ mExt ms r.val) (hξ₂ : ξ₂ ≠ 0) :
    q = M := by
  have hd := hasDerivAt_parisiFunctional_qUpdate ms qs r hX₀ hξ hξ'
  have hz := hmin.hasDerivAt_eq_zero hd
  have hc : (1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) * ξ₂ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) hξ₂
    exact sub_ne_zero.mpr hm
  have hz' :
      ((1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) * ξ₂) * (-M + q) = 0 := by
    simpa [mul_assoc] using hz
  have hlast : -M + q = 0 := (mul_eq_zero.mp hz').resolve_left hc
  linarith

/-- The stationarity implication with the nonvanishing mass gap derived from (14.103). -/
theorem parisiQ_eq_moment_of_isLocalMin_of_admissible
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) {q ξ₂ M : ℝ} (hm : ParisiMAdmissible ms) (hξ₂ : 0 < ξ₂)
    (hmin : IsLocalMin (fun u => parisiFunctional ξ h ms (qUpdate qs r u)) q)
    (hX₀ : HasDerivAt
      (fun u => parisiX₀ ξ ms (qUpdate qs r u) (fun x => Real.log (Real.cosh (h + x))))
      ((-1 / 2 : ℝ) * ξ₂ * (mExt ms (r.val + 1) - mExt ms r.val) * M) q)
    (hξ : HasDerivAt ξ (deriv ξ q) q)
    (hξ' : HasDerivAt (deriv ξ) ξ₂ q) :
    q = M := by
  apply parisiQ_eq_moment_of_isLocalMin ms qs r hmin hX₀ hξ hξ'
  · exact ne_of_gt (hm.mExt_gap_pos r) |>.imp fun heq => sub_eq_zero.mpr heq
  · exact ne_of_gt hξ₂

/-- Proposition 14.7.5, in the overlap-coordinate API.

The functions `M` and `ξ₂` record respectively
`E(W₁ ⋯ W_{r-1} A'_r(ζ_r)^2)` and `ξ''(q_r)`. The endpoint assumptions are the two strict
bounds used in Talagrand's proof: the first moment is positive and the last moment is less than
one. Admissible global minimality then gives the strict extended overlap chain (14.221), and
the derivative identity (14.220) gives all the equations (14.222). -/
theorem parisiQ_strict_chain_and_eq_moment_of_isMin
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (M ξ₂ : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hmin : IsParisiQMinimizer ξ h ms qs)
    (hX₀ : ∀ r, HasDerivAt
      (fun u => parisiX₀ ξ ms (qUpdate qs r u) (fun x => Real.log (Real.cosh (h + x))))
      ((-1 / 2 : ℝ) * ξ₂ r * (mExt ms (r.val + 1) - mExt ms r.val) * M r) (qs r))
    (hξ : ∀ r, HasDerivAt ξ (deriv ξ (qs r)) (qs r))
    (hξ' : ∀ r, HasDerivAt (deriv ξ) (ξ₂ r) (qs r))
    (hξ₂ : ∀ r, 0 < ξ₂ r) (hMfirst : 0 < M 0) (hMlast : M (Fin.last k) < 1) :
    (∀ r : ℕ, r ≤ k + 1 → qExt qs r < qExt qs (r + 1)) ∧
      ∀ r, qs r = M r := by
  have hd (r : Fin (k + 1)) :=
    hasDerivAt_parisiFunctional_qUpdate ms qs r (hX₀ r) (hξ r) (hξ' r)
  have hq0 : 0 < qs 0 := by
    by_contra hn
    have hz : qs 0 = 0 := le_antisymm (not_lt.mp hn) hmin.1.2.1
    have hnonneg := hmin.first_deriv_nonneg hz (hd 0)
    have hgap : 0 < mExt ms ((0 : Fin (k + 1)).val + 1) -
        mExt ms (0 : Fin (k + 1)).val := hm.mExt_gap_pos 0
    have hcoef : 0 < (1 / 2 : ℝ) *
        (mExt ms ((0 : Fin (k + 1)).val + 1) - mExt ms (0 : Fin (k + 1)).val) * ξ₂ 0 :=
      mul_pos (mul_pos (by norm_num) hgap) (hξ₂ 0)
    have hneg : -M 0 + qs 0 < 0 := by rw [hz]; linarith
    nlinarith
  have hq1 : qs (Fin.last k) < 1 := by
    by_contra hn
    have ho : qs (Fin.last k) = 1 := le_antisymm hmin.1.2.2 (not_lt.mp hn)
    have hnonpos := hmin.last_deriv_nonpos ho (hd (Fin.last k))
    have hgap : 0 < mExt ms ((Fin.last k).val + 1) - mExt ms (Fin.last k).val :=
      hm.mExt_gap_pos (Fin.last k)
    have hcoef : 0 < (1 / 2 : ℝ) *
        (mExt ms ((Fin.last k).val + 1) - mExt ms (Fin.last k).val) * ξ₂ (Fin.last k) :=
      mul_pos (mul_pos (by norm_num) hgap) (hξ₂ (Fin.last k))
    have hpos : 0 < -M (Fin.last k) + qs (Fin.last k) := by rw [ho]; linarith
    nlinarith
  refine ⟨fun r hr => qExt_strict_succ hmin.1.1 hq0 hq1 hr, ?_⟩
  intro r
  exact parisiQ_eq_moment_of_isLocalMin_of_admissible ms qs r hm (hξ₂ r)
    (hmin.isLocalMin_qUpdate ms qs hq0 hq1 r) (hX₀ r) (hξ r) (hξ' r)

end

end SpinGlass
