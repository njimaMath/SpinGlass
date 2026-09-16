/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.ParisiFunctional
import SpinGlass.Parisi.RandomFieldFunctional
import Common.Mathlib.Analysis.SpecialFunctions.Tanh
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
* `parisiQ_strict_chain_and_eq_moment_of_isMin`: a conditional abstract reduction of
  Proposition 14.7.5.
* `hasDerivAt_randomFieldParisiFunctional_qUpdate`: (14.220) after averaging an i.i.d.
  external-field coordinate.
* `randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin`: Proposition 14.7.5
  derived from the recursion, the covariance condition, and a nondegenerate probability law.
* `iidExternalFieldParisiQ_strict_chain_and_eq_moment_of_isMin`: the same result with the
  moment explicitly identified as an i.i.d. product-coordinate expectation.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

/-! ### Spatial derivatives of a Cole-Hopf iterate -/

/-- The recursively propagated first spatial derivative of a Cole-Hopf iterate. -/
noncomputable def coleHopfIterateDeriv : (j : ℕ) → (Fin j → ℝ) → (Fin j → ℝ≥0)
    → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | 0, _, _, _, G' => G'
  | j + 1, ms, vs, G, G' => fun x =>
      ∫ z, coleHopfIterateDeriv j (Fin.tail ms) (Fin.tail vs) G G' (x + z)
          * coleHopfQ (ms 0) (vs 0)
              (coleHopfIterate j (Fin.tail ms) (Fin.tail vs) G) x z
        ∂gaussianReal 0 (vs 0)

/-- The recursively propagated second spatial derivative of a Cole-Hopf iterate. -/
noncomputable def coleHopfIterateDeriv2 : (j : ℕ) → (Fin j → ℝ) → (Fin j → ℝ≥0)
    → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | 0, _, _, _, _, G'' => G''
  | j + 1, ms, vs, G, G', G'' => fun x =>
      (∫ z, (coleHopfIterateDeriv2 j (Fin.tail ms) (Fin.tail vs) G G' G'' (x + z)
            + ms 0 * coleHopfIterateDeriv j (Fin.tail ms) (Fin.tail vs) G G' (x + z) ^ 2)
          * coleHopfQ (ms 0) (vs 0)
              (coleHopfIterate j (Fin.tail ms) (Fin.tail vs) G) x z
        ∂gaussianReal 0 (vs 0))
        - ms 0 * coleHopfIterateDeriv (j + 1) ms vs G G' x ^ 2

lemma coleHopfIterate_eq_terminal_of_eq_zero {j : ℕ} (hj : j = 0)
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (G : ℝ → ℝ) :
    coleHopfIterate j ms vs G = G := by
  subst j
  rfl

lemma coleHopfIterateDeriv_eq_terminal_of_eq_zero {j : ℕ} (hj : j = 0)
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (G G' : ℝ → ℝ) :
    coleHopfIterateDeriv j ms vs G G' = G' := by
  subst j
  rfl

lemma coleHopf_translate (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (c x : ℝ) :
    coleHopf m v (fun y => A (c + y)) x = coleHopf m v A (c + x) := by
  unfold coleHopf
  split_ifs
  · apply integral_congr_ae
    filter_upwards [] with z
    congr 1
    ring
  · congr 2
    apply integral_congr_ae
    filter_upwards [] with z
    congr 3
    ring

lemma coleHopfQ_translate (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (c x z : ℝ) :
    coleHopfQ m v (fun y => A (c + y)) x z = coleHopfQ m v A (c + x) z := by
  unfold coleHopfQ
  rw [coleHopf_translate]
  congr 3
  ring

theorem coleHopfIterate_translate {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (G : ℝ → ℝ) (c x : ℝ) :
    coleHopfIterate j ms vs (fun y => G (c + y)) x =
      coleHopfIterate j ms vs G (c + x) := by
  induction j generalizing c x with
  | zero => rfl
  | succ j ih =>
      rw [coleHopfIterate_succ, coleHopfIterate_succ]
      have htail : coleHopfIterate j (Fin.tail ms) (Fin.tail vs) (fun y => G (c + y)) =
          fun y => coleHopfIterate j (Fin.tail ms) (Fin.tail vs) G (c + y) := by
        funext y
        exact ih (Fin.tail ms) (Fin.tail vs) c y
      rw [htail, coleHopf_translate]

theorem coleHopfIterateDeriv_translate {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (G G' : ℝ → ℝ) (c x : ℝ) :
    coleHopfIterateDeriv j ms vs (fun y => G (c + y)) (fun y => G' (c + y)) x =
      coleHopfIterateDeriv j ms vs G G' (c + x) := by
  induction j generalizing c x with
  | zero => rfl
  | succ j ih =>
      rw [coleHopfIterateDeriv, coleHopfIterateDeriv]
      have htail : coleHopfIterate j (Fin.tail ms) (Fin.tail vs) (fun y => G (c + y)) =
          fun y => coleHopfIterate j (Fin.tail ms) (Fin.tail vs) G (c + y) := by
        funext y
        exact coleHopfIterate_translate (Fin.tail ms) (Fin.tail vs) G c y
      rw [htail]
      apply integral_congr_ae
      filter_upwards [] with z
      rw [ih (Fin.tail ms) (Fin.tail vs) c (x + z), coleHopfQ_translate]
      congr 2
      ring

/-- Bounded first and second derivatives propagate through every positive-exponent Cole-Hopf
level.  The derivative functions are the canonical tilted-integral recursions above. -/
theorem coleHopfIterate_deriv_regular {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    {G G' G'' : ℝ → ℝ}
    (hG : ∀ x, HasDerivAt G (G' x) x) (hG' : ∀ x, HasDerivAt G' (G'' x) x)
    (hG''c : Continuous G'') {L L₂ : ℝ} (hL : ∀ x, |G' x| ≤ L)
    (hL₂ : ∀ x, |G'' x| ≤ L₂) (hpos : ∀ i, 0 < ms i) :
    (∀ x, HasDerivAt (coleHopfIterate j ms vs G)
      (coleHopfIterateDeriv j ms vs G G' x) x) ∧
    (∃ C : ℝ,
      (∀ x, HasDerivAt (coleHopfIterateDeriv j ms vs G G')
        (coleHopfIterateDeriv2 j ms vs G G' G'' x) x) ∧
      Continuous (coleHopfIterateDeriv2 j ms vs G G' G'') ∧
      (∀ x, |coleHopfIterateDeriv j ms vs G G' x| ≤ L) ∧
      ∀ x, |coleHopfIterateDeriv2 j ms vs G G' G'' x| ≤ C) := by
  induction j with
  | zero =>
      refine ⟨hG, L₂, hG', hG''c, hL, hL₂⟩
  | succ j ih =>
      let ims : Fin j → ℝ := Fin.tail ms
      let ivs : Fin j → ℝ≥0 := Fin.tail vs
      let A : ℝ → ℝ := coleHopfIterate j ims ivs G
      let A' : ℝ → ℝ := coleHopfIterateDeriv j ims ivs G G'
      let A'' : ℝ → ℝ := coleHopfIterateDeriv2 j ims ivs G G' G''
      have hposi : ∀ i, 0 < ims i := fun i => hpos i.succ
      obtain ⟨hA, C, hA', hA''c, hA'b, hA''b⟩ := ih ims ivs hposi
      have hAg : HasLinearGrowth A := HasLinearGrowth.of_bounded_deriv hA hA'b
      have hA'g : HasExpGrowth A' := HasExpGrowth.of_bounded hA'b
      have hA''g : HasExpGrowth A'' := HasExpGrowth.of_bounded hA''b
      have hA'm : Measurable A' := measurable_of_hasDerivAt hA'
      have hm : ms 0 ≠ 0 := (hpos 0).ne'
      let B : ℝ → ℝ := coleHopf (ms 0) (vs 0) A
      let B' : ℝ → ℝ := fun x =>
        ∫ z, A' (x + z) * coleHopfQ (ms 0) (vs 0) A x z ∂gaussianReal 0 (vs 0)
      let B'' : ℝ → ℝ := fun x =>
        (∫ z, (A'' (x + z) + ms 0 * A' (x + z) ^ 2)
            * coleHopfQ (ms 0) (vs 0) A x z ∂gaussianReal 0 (vs 0))
          - ms 0 * B' x ^ 2
      have hB : ∀ x, HasDerivAt B (B' x) x := fun x =>
        hasDerivAt_coleHopf hA hAg hA'g hA'm hm (vs 0) x
      have hB' : ∀ x, HasDerivAt B' (B'' x) x := fun x =>
        hasDerivAt_integral_deriv_mul_coleHopfQ hA hA' hAg hA'g hA''g hA''c.measurable
          hm (vs 0) x
      have hB'b : ∀ x, |B' x| ≤ L := fun x =>
        abs_integral_mul_coleHopfQ_le hAg (measurable_of_hasDerivAt hA) hm hA'm hA'b
          (vs 0) x
      have hA'c : Continuous A' :=
        continuous_iff_continuousAt.2 fun x => (hA' x).continuousAt
      have hBc : Continuous A :=
        continuous_iff_continuousAt.2 fun x => (hA x).continuousAt
      have hB'c : Continuous B' :=
        continuous_iff_continuousAt.2 fun x => (hB' x).continuousAt
      have hinnerc : Continuous fun x => A'' x + ms 0 * A' x ^ 2 :=
        hA''c.add (continuous_const.mul (hA'c.pow 2))
      have hinnerb : ∀ x, |A'' x + ms 0 * A' x ^ 2| ≤ C + |ms 0| * L ^ 2 := by
        intro x
        calc
          |A'' x + ms 0 * A' x ^ 2| ≤ |A'' x| + |ms 0 * A' x ^ 2| := abs_add_le _ _
          _ ≤ C + |ms 0| * L ^ 2 := by
            rw [abs_mul, abs_pow]
            gcongr
            exact hA''b x
            exact hA'b x
      have hinnerg : HasExpGrowth fun x => A'' x + ms 0 * A' x ^ 2 :=
        HasExpGrowth.of_bounded hinnerb
      have hIc : Continuous fun x =>
          ∫ z, (A'' (x + z) + ms 0 * A' (x + z) ^ 2)
            * coleHopfQ (ms 0) (vs 0) A x z ∂gaussianReal 0 (vs 0) :=
        continuous_integral_mul_coleHopfQ hinnerc hinnerg hBc hAg hm (vs 0)
      have hB''c : Continuous B'' := hIc.sub (continuous_const.mul (hB'c.pow 2))
      have hIb : ∀ x, |∫ z, (A'' (x + z) + ms 0 * A' (x + z) ^ 2)
          * coleHopfQ (ms 0) (vs 0) A x z ∂gaussianReal 0 (vs 0)|
          ≤ C + |ms 0| * L ^ 2 := fun x =>
        abs_integral_mul_coleHopfQ_le hAg (measurable_of_hasDerivAt hA) hm
          hinnerc.measurable hinnerb (vs 0) x
      have hB''b : ∀ x, |B'' x| ≤ C + 2 * |ms 0| * L ^ 2 := by
        intro x
        calc
          |B'' x| ≤ |∫ z, (A'' (x + z) + ms 0 * A' (x + z) ^ 2)
                * coleHopfQ (ms 0) (vs 0) A x z ∂gaussianReal 0 (vs 0)|
              + |ms 0 * B' x ^ 2| := by
            dsimp [B'']
            exact abs_sub _ _
          _ ≤ (C + |ms 0| * L ^ 2) + |ms 0| * L ^ 2 := by
            rw [abs_mul, abs_pow]
            gcongr
            exact hIb x
            exact hB'b x
          _ = C + 2 * |ms 0| * L ^ 2 := by ring
      change
        (∀ x, HasDerivAt B (B' x) x) ∧
          ∃ C', (∀ x, HasDerivAt B' (B'' x) x) ∧ Continuous B'' ∧
            (∀ x, |B' x| ≤ L) ∧ ∀ x, |B'' x| ≤ C'
      exact ⟨hB, C + 2 * |ms 0| * L ^ 2, hB', hB''c, hB'b, hB''b⟩

/-- Strict positivity of the terminal second derivative propagates through every
positive-exponent Cole-Hopf level. -/
theorem coleHopfIterateDeriv2_pos {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    {G G' G'' : ℝ → ℝ}
    (hG : ∀ x, HasDerivAt G (G' x) x) (hG' : ∀ x, HasDerivAt G' (G'' x) x)
    (hG''c : Continuous G'') {L L₂ : ℝ} (hL : ∀ x, |G' x| ≤ L)
    (hL₂ : ∀ x, |G'' x| ≤ L₂) (hG''pos : ∀ x, 0 < G'' x)
    (hpos : ∀ i, 0 < ms i) :
    ∀ x, 0 < coleHopfIterateDeriv2 j ms vs G G' G'' x := by
  induction j with
  | zero => exact hG''pos
  | succ j ih =>
      let ims : Fin j → ℝ := Fin.tail ms
      let ivs : Fin j → ℝ≥0 := Fin.tail vs
      let A : ℝ → ℝ := coleHopfIterate j ims ivs G
      let A' : ℝ → ℝ := coleHopfIterateDeriv j ims ivs G G'
      let A'' : ℝ → ℝ := coleHopfIterateDeriv2 j ims ivs G G' G''
      have hposi : ∀ i, 0 < ims i := fun i => hpos i.succ
      obtain ⟨hA, C, hA', hA''c, hA'b, hA''b⟩ :=
        coleHopfIterate_deriv_regular ims ivs hG hG' hG''c hL hL₂ hposi
      have hA''pos : ∀ x, 0 < A'' x := ih ims ivs hposi
      have hAg : HasLinearGrowth A := HasLinearGrowth.of_bounded_deriv hA hA'b
      have hAm : Measurable A := measurable_of_hasDerivAt hA
      have hA'g : HasExpGrowth A' := HasExpGrowth.of_bounded hA'b
      have hA'm : Measurable A' := measurable_of_hasDerivAt hA'
      have hA''g : HasExpGrowth A'' := HasExpGrowth.of_bounded hA''b
      have hA''m : Measurable A'' := hA''c.measurable
      have hm : ms 0 ≠ 0 := (hpos 0).ne'
      intro x
      let Q : ℝ → ℝ := coleHopfQ (ms 0) (vs 0) A x
      let d : ℝ := ∫ z, A' (x + z) * Q z ∂gaussianReal 0 (vs 0)
      have hi2 : Integrable (fun z => A'' (x + z) * Q z) (gaussianReal 0 (vs 0)) :=
        integrable_mul_coleHopfQ hAg hAm hm hA''g hA''m (vs 0) x
      have hip : 0 < ∫ z, A'' (x + z) * Q z ∂gaussianReal 0 (vs 0) := by
        rw [integral_pos_iff_support_of_nonneg
          (fun z => mul_nonneg (hA''pos (x + z)).le (coleHopfQ_pos _ _ _ _ _).le) hi2]
        have hsupp : Function.support (fun z => A'' (x + z) * Q z) = Set.univ := by
          ext z
          simp only [Function.mem_support, mem_univ, iff_true]
          exact ne_of_gt (mul_pos (hA''pos (x + z)) (coleHopfQ_pos _ _ _ _ _))
        rw [hsupp, measure_univ]
        norm_num
      have hiSq : Integrable (fun z => A' (x + z) ^ 2 * Q z)
          (gaussianReal 0 (vs 0)) :=
        integrable_mul_coleHopfQ hAg hAm hm (hA'g.pow 2) (hA'm.pow_const 2) (vs 0) x
      have hvar : d ^ 2 ≤ ∫ z, A' (x + z) ^ 2 * Q z ∂gaussianReal 0 (vs 0) := by
        exact sq_integral_mul_coleHopfQ_le hAg hAm hm hA'g hA'm (vs 0) x
      have hsplit :
          (∫ z, (A'' (x + z) + ms 0 * A' (x + z) ^ 2) * Q z
            ∂gaussianReal 0 (vs 0)) =
            (∫ z, A'' (x + z) * Q z ∂gaussianReal 0 (vs 0)) +
              ms 0 * ∫ z, A' (x + z) ^ 2 * Q z ∂gaussianReal 0 (vs 0) := by
        have himul : Integrable (fun z => ms 0 * (A' (x + z) ^ 2 * Q z))
            (gaussianReal 0 (vs 0)) := hiSq.const_mul _
        calc
          (∫ z, (A'' (x + z) + ms 0 * A' (x + z) ^ 2) * Q z
              ∂gaussianReal 0 (vs 0)) =
              ∫ z, A'' (x + z) * Q z + ms 0 * (A' (x + z) ^ 2 * Q z)
                ∂gaussianReal 0 (vs 0) := by
                  apply integral_congr_ae
                  filter_upwards [] with z
                  ring
          _ = (∫ z, A'' (x + z) * Q z ∂gaussianReal 0 (vs 0)) +
              ∫ z, ms 0 * (A' (x + z) ^ 2 * Q z) ∂gaussianReal 0 (vs 0) :=
                integral_add hi2 himul
          _ = (∫ z, A'' (x + z) * Q z ∂gaussianReal 0 (vs 0)) +
              ms 0 * ∫ z, A' (x + z) ^ 2 * Q z ∂gaussianReal 0 (vs 0) := by
                rw [integral_const_mul]
      change (∫ z, (A'' (x + z) + ms 0 * A' (x + z) ^ 2) * Q z
          ∂gaussianReal 0 (vs 0)) - ms 0 * d ^ 2 > 0
      rw [hsplit]
      nlinarith [hpos 0]

/-- Differentiate a positive-variance final Cole--Hopf level, followed by a fixed prefix and a
fixed root Gaussian average.  The additive affine term is the contribution of the absorbed
exponent-one terminal level. -/
theorem hasDerivAt_integral_coleHopfIterate_absorbed_last
    {j : ℕ} (ps : Fin j → ℝ) (pvs : Fin j → ℝ≥0)
    (hpos : ∀ i, 0 < ps i) (hle : ∀ i, ps i ≤ 1)
    {m a s₀ : ℝ} (hm : 0 ≤ m) (hma : m ≤ 1) (hs₀ : 0 < s₀)
    {A A' A'' : ℝ → ℝ}
    (hA : ∀ y, HasDerivAt A (A' y) y)
    (hA' : ∀ y, HasDerivAt A' (A'' y) y)
    (hA''c : Continuous A'') (hA'b : ∀ y, |A' y| ≤ 1)
    (hA''b : ∀ y, |A'' y| ≤ 1) (w₀ : ℝ≥0) :
    HasDerivAt
      (fun s => ∫ z₀, coleHopfIterate j ps pvs
        (fun y => coleHopf m (Real.toNNReal s) A y
          + (a - s) / 2) z₀ ∂gaussianReal 0 w₀)
      (∫ z₀, ∫ zs,
        ((1 / 2 : ℝ) * ∫ z,
            (A'' (z₀ + ∑ p, zs p + z) +
              m * A' (z₀ + ∑ p, zs p + z) ^ 2) *
              coleHopfQ m (Real.toNNReal s₀) A
                (z₀ + ∑ p, zs p) z ∂gaussianReal 0 (Real.toNNReal s₀) - 1 / 2)
          ∂cascadeTiltMeasure j ps (fun p => gaussianReal 0 (pvs p))
            (fun zs => ENNReal.ofReal (Real.exp
              (coleHopf m (Real.toNNReal s₀) A
                (z₀ + ∑ p, zs p) + (a - s₀) / 2)))
        ∂gaussianReal 0 w₀) s₀ := by
  let Φ : ℝ → ℝ → ℝ := fun s y => coleHopf m (Real.toNNReal s) A y + (a - s) / 2
  let D : ℝ → ℝ → ℝ := fun s y =>
    (1 / 2 : ℝ) * ∫ z, (A'' (y + z) + m * A' (y + z) ^ 2) *
      coleHopfQ m (Real.toNNReal s) A y z ∂gaussianReal 0 (Real.toNNReal s) - 1 / 2
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun y => (hA y).continuousAt
  have hA'c : Continuous A' := continuous_iff_continuousAt.2 fun y => (hA' y).continuousAt
  have hAg : HasLinearGrowth A := HasLinearGrowth.of_bounded_deriv hA hA'b
  have hA'g : HasExpGrowth A' := HasExpGrowth.of_bounded hA'b
  have hA''g : HasExpGrowth A'' := HasExpGrowth.of_bounded hA''b
  have hAm : Measurable A := hAc.measurable
  have hA'm : Measurable A' := hA'c.measurable
  have hinnerb : ∀ y, |A'' y + m * A' y ^ 2| ≤ 1 + |m| := by
    intro y
    calc
      |A'' y + m * A' y ^ 2| ≤ |A'' y| + |m * A' y ^ 2| := abs_add_le _ _
      _ = |A'' y| + |m| * |A' y| ^ 2 := by rw [abs_mul, abs_pow]
      _ ≤ 1 + |m| := by
        have hsquare : |A' y| ^ 2 ≤ 1 := by
          nlinarith [abs_nonneg (A' y), hA'b y]
        exact add_le_add (hA''b y)
          (by simpa using mul_le_mul_of_nonneg_left hsquare (abs_nonneg m))
  have hDmeas : ∀ s, Measurable (D s) := by
    intro s
    dsimp [D]
    exact ((continuous_const.mul (continuous_integral_mul_coleHopfQ'
      hAc hAg m (hA''c.add (continuous_const.mul (hA'c.pow 2)))
      (hA''g.add ((hA'g.pow 2).const_mul m)) (Real.toNNReal s))).sub
        continuous_const).measurable
  let δ : ℝ := s₀ / 2
  have hδ : 0 < δ := half_pos hs₀
  have hspos : ∀ s ∈ Metric.ball s₀ δ, 0 < s := by
    intro s hs
    have habs : |s - s₀| < s₀ / 2 := by simpa [δ, Real.dist_eq] using hs
    linarith [neg_abs_le (s - s₀)]
  have hd : ∀ s ∈ Metric.ball s₀ δ, ∀ y, HasDerivAt (fun s => Φ s y) (D s y) s := by
    intro s hs y
    have hv : HasDerivAt (fun t => coleHopf m (Real.toNNReal t) A y)
        ((1 / 2 : ℝ) * ∫ z, (A'' (y + z) + m * A' (y + z) ^ 2) *
          coleHopfQ m (Real.toNNReal s) A y z ∂gaussianReal 0 (Real.toNNReal s)) s := by
      rcases hm.eq_or_lt with rfl | hmpos
      · have hv₀ := ProbabilityTheory.hasDerivAt_integral_comp_add_gaussianReal_var
          hA hA' hAg.toHasExpGrowth hA'g hA''g hA''c (hspos s hs) y
        simpa [coleHopf_zero, coleHopfQ_zero] using hv₀
      · exact ProbabilityTheory.hasDerivAt_coleHopf_var hA hA' hAg hA'g hA''g
          hA''c hmpos.ne' (hspos s hs) y
    have hc : HasDerivAt (fun s : ℝ => (a - s) / 2) (-(1 / 2)) s := by
      have hc' := ((hasDerivAt_const s a).sub (hasDerivAt_id s)).div_const 2
      have heq : (-1 / 2 : ℝ) = -(1 / 2) := by ring
      rw [← heq]
      simpa using hc'
    have hfun : (fun t : ℝ => coleHopf m (Real.toNNReal t) A y + (a - t) / 2) =
        (fun t => coleHopf m (Real.toNNReal t) A y) + fun t => (a - t) / 2 := by
      funext t
      rfl
    rw [show (fun t => Φ t y) =
      (fun t => coleHopf m (Real.toNNReal t) A y + (a - t) / 2) by rfl, hfun]
    simpa only [D, sub_eq_add_neg] using hv.add hc
  have hDb : ∀ s ∈ Metric.ball s₀ δ, ∀ y, |D s y| ≤ (1 + |m|) / 2 + 1 / 2 := by
    intro s hs y
    have hi := abs_integral_mul_coleHopfQ_le' hAg hAm m
      ((hA''c.add (continuous_const.mul (hA'c.pow 2))).measurable) hinnerb
      (Real.toNNReal s) y
    change |∫ z, (A'' (y + z) + m * A' (y + z) ^ 2) *
      coleHopfQ m (Real.toNNReal s) A y z ∂gaussianReal 0 (Real.toNNReal s)| ≤
        1 + |m| at hi
    dsimp [D]
    calc
      |(1 / 2 : ℝ) * ∫ z, (A'' (y + z) + m * A' (y + z) ^ 2) *
          coleHopfQ m (Real.toNNReal s) A y z ∂gaussianReal 0 (Real.toNNReal s) - 1 / 2| ≤
          (1 / 2) * |∫ z, (A'' (y + z) + m * A' (y + z) ^ 2) *
            coleHopfQ m (Real.toNNReal s) A y z ∂gaussianReal 0 (Real.toNNReal s)| +
            1 / 2 := by
              calc
                _ ≤ |(1 / 2 : ℝ) * ∫ z, (A'' (y + z) + m * A' (y + z) ^ 2) *
                    coleHopfQ m (Real.toNNReal s) A y z
                      ∂gaussianReal 0 (Real.toNNReal s)| + |(1 / 2 : ℝ)| := abs_sub _ _
                _ = _ := by rw [abs_mul]; norm_num
      _ ≤ (1 + |m|) / 2 + 1 / 2 := by
        have hi' : (1 / 2 : ℝ) * |∫ z, (A'' (y + z) + m * A' (y + z) ^ 2) *
            coleHopfQ m (Real.toNNReal s) A y z ∂gaussianReal 0 (Real.toNNReal s)| ≤
              (1 + |m|) / 2 := by
          calc
            _ ≤ (1 / 2 : ℝ) * (1 + |m|) :=
              mul_le_mul_of_nonneg_left hi (by norm_num)
            _ = _ := by ring
        simpa only [add_comm] using add_le_add_right hi' (1 / 2)
  have hΦlip : ∀ s x y, |Φ s y - Φ s x| ≤ 1 * |y - x| := by
    intro s x y
    dsimp [Φ]
    rw [add_sub_add_right_eq_sub]
    exact abs_coleHopf_sub_le_of_lipschitz m hAm
      (ProbabilityTheory.abs_sub_le_mul_abs_sub_of_hasDerivAt hA hA'b)
      (Real.toNNReal s) x y
  let Ψ : ℝ → ℝ → ℝ := fun s => coleHopfIterate j ps pvs (Φ s)
  let E : ℝ → ℝ → ℝ := fun s y =>
    ∫ zs, D s (y + ∑ p, zs p)
      ∂cascadeTiltMeasure j ps (fun p => gaussianReal 0 (pvs p))
        (fun zs => ENNReal.ofReal (Real.exp (Φ s (y + ∑ p, zs p))))
  have hΨd : ∀ s ∈ Metric.ball s₀ δ, ∀ y, HasDerivAt (fun s => Ψ s y) (E s y) s := by
    intro s hs y
    let ρ : ℝ := δ - dist s s₀
    have hρ : 0 < ρ := sub_pos.mpr (Metric.mem_ball.1 hs)
    have hsub : Metric.ball s ρ ⊆ Metric.ball s₀ δ := by
      intro t ht
      rw [Metric.mem_ball] at ht ⊢
      calc
        dist t s₀ ≤ dist t s + dist s s₀ := dist_triangle _ _ _
        _ < ρ + dist s s₀ := by linarith
        _ = δ := by dsimp [ρ]; ring
    exact hasDerivAt_coleHopfIterate_ball ps pvs hρ hpos hle hDmeas
      (fun t ht => hd t (hsub ht)) (fun t ht => hDb t (hsub ht)) hΦlip y
  have hΨlip : ∀ s x y, |Ψ s y - Ψ s x| ≤ 1 * |y - x| := fun s =>
    abs_coleHopfIterate_sub_le j ps pvs
      ((lipschitzWith_toNNReal_of_abs_sub_le (hΦlip s)).continuous.measurable)
      (hΦlip s)
  have hEb : ∀ s ∈ Metric.ball s₀ δ, ∀ y, |E s y| ≤ (1 + |m|) / 2 + 1 / 2 := by
    intro s hs y
    exact abs_integral_cascadeTiltMeasure_le ps pvs hpos hle
      ((lipschitzWith_toNNReal_of_abs_sub_le (hΦlip s)).continuous.measurable)
      (hΦlip s) y (hDb s hs)
  have hout := hasDerivAt_integral_gaussianReal_param hδ hΨlip hΨd hEb w₀ 0
  simpa [Ψ, E, Φ, D] using hout

/-- Concatenating two finite arrays of levels composes their Cole-Hopf iterates. -/
theorem coleHopfIterate_append (i j : ℕ)
    (ms₁ : Fin i → ℝ) (vs₁ : Fin i → ℝ≥0)
    (ms₂ : Fin j → ℝ) (vs₂ : Fin j → ℝ≥0) (G : ℝ → ℝ) :
    coleHopfIterate (i + j) (Fin.append ms₁ ms₂) (Fin.append vs₁ vs₂) G =
      coleHopfIterate i ms₁ vs₁ (coleHopfIterate j ms₂ vs₂ G) := by
  have hp : (fun p => (Fin.append ms₁ ms₂ p, Fin.append vs₁ vs₂ p)) =
      Fin.append (fun p => (ms₁ p, vs₁ p)) (fun p => (ms₂ p, vs₂ p)) := by
    funext p
    refine Fin.addCases (fun q => ?_) (fun q => ?_) p
    · simp
    · simp
  rw [coleHopfIterate_eq_list, coleHopfIterate_eq_list, coleHopfIterate_eq_list,
    hp, List.ofFn_fin_append, coleHopfIterateList_append]

/-- An array is the concatenation of its prefix, next two entries, and suffix. -/
lemma fin_append_two_slices {α : Type} (j s : ℕ) (a : Fin (j + (2 + s)) → α) :
    Fin.append (fun p : Fin j => a ⟨p.val, by omega⟩)
      (Fin.append (fun p : Fin 2 => a ⟨j + p.val, by omega⟩)
        (fun p : Fin s => a ⟨j + 2 + p.val, by omega⟩)) = a := by
  funext p
  refine Fin.addCases (fun q => ?_) (fun q => ?_) p
  · simp
    congr 1
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) q
    · simp
      congr 1
    · simp
      apply congrArg a
      apply Fin.ext
      simp
      omega

/-- Split a Cole-Hopf iterate into a prefix, two consecutive levels, and a suffix. -/
theorem coleHopfIterate_split_two (i s : ℕ)
    (ms : Fin (i + (2 + s)) → ℝ) (vs : Fin (i + (2 + s)) → ℝ≥0) (G : ℝ → ℝ) :
    coleHopfIterate (i + (2 + s)) ms vs G =
      coleHopfIterate i
        (fun p => ms ⟨p.val, by omega⟩) (fun p => vs ⟨p.val, by omega⟩)
        (coleHopf (ms ⟨i, by omega⟩) (vs ⟨i, by omega⟩)
          (coleHopf (ms ⟨i + 1, by omega⟩) (vs ⟨i + 1, by omega⟩)
            (coleHopfIterate s
              (fun p => ms ⟨i + p.val + 2, by omega⟩)
              (fun p => vs ⟨i + p.val + 2, by omega⟩) G))) := by
  conv_lhs =>
    rw [← fin_append_two_slices i s ms, ← fin_append_two_slices i s vs]
  rw [coleHopfIterate_append, coleHopfIterate_append]
  rw [coleHopfIterate_succ, coleHopfIterate_succ, coleHopfIterate_zero]
  congr 4
  all_goals
    funext p
    apply congrArg _
    apply Fin.ext
    simp
    omega

/-- The two-level split with an arbitrary, propositionally equal total length. -/
theorem coleHopfIterate_split_two_of_eq {n : ℕ} (i s : ℕ) (hn : n = i + (2 + s))
    (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0) (G : ℝ → ℝ) :
    coleHopfIterate n ms vs G =
      coleHopfIterate i
        (fun p => ms ⟨p.val, by omega⟩) (fun p => vs ⟨p.val, by omega⟩)
        (coleHopf (ms ⟨i, by omega⟩) (vs ⟨i, by omega⟩)
          (coleHopf (ms ⟨i + 1, by omega⟩) (vs ⟨i + 1, by omega⟩)
            (coleHopfIterate s
              (fun p => ms ⟨i + p.val + 2, by omega⟩)
              (fun p => vs ⟨i + p.val + 2, by omega⟩) G))) := by
  subst n
  exact coleHopfIterate_split_two i s ms vs G

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

lemma coleHopfSplitMoment_translate (m m' : ℝ) (vR vL : ℝ≥0)
    (A A' : ℝ → ℝ) (c x : ℝ) :
    coleHopfSplitMoment m m' vR vL (fun y => A (c + y)) (fun y => A' (c + y)) x =
      coleHopfSplitMoment m m' vR vL A A' (c + x) := by
  have hB : coleHopf m vR (fun y => A (c + y)) =
      fun y => coleHopf m vR A (c + y) := by
    funext y
    exact coleHopf_translate m vR A c y
  unfold coleHopfSplitMoment
  rw [hB]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [coleHopfQ_translate]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with w
  rw [coleHopfQ_translate]
  congr 2 <;> ring

/-- A split moment is bounded by one whenever the terminal derivative is bounded by one. -/
lemma abs_coleHopfSplitMoment_le_one {m m' : ℝ} {vR vL : ℝ≥0}
    {A A' A'' : ℝ → ℝ} (hA : ∀ y, HasDerivAt A (A' y) y)
    (hA' : ∀ y, HasDerivAt A' (A'' y) y) (hA'b : ∀ y, |A' y| ≤ 1) (x : ℝ) :
    |coleHopfSplitMoment m m' vR vL A A' x| ≤ 1 := by
  have hAm : Measurable A := measurable_of_hasDerivAt hA
  have hA'm : Measurable A' := measurable_of_hasDerivAt hA'
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun y => (hA y).continuousAt
  have hA'c : Continuous A' := continuous_iff_continuousAt.2 fun y => (hA' y).continuousAt
  have hAg : HasLinearGrowth A := HasLinearGrowth.of_bounded_deriv hA hA'b
  have hA'g : HasExpGrowth A' := HasExpGrowth.of_bounded hA'b
  have hAlip : ∀ y z, |A z - A y| ≤ 1 * |z - y| :=
    ProbabilityTheory.abs_sub_le_mul_abs_sub_of_hasDerivAt hA hA'b
  let B : ℝ → ℝ := coleHopf m vR A
  let D : ℝ → ℝ := fun y =>
    ∫ w, A' (y + w) * coleHopfQ m vR A y w ∂gaussianReal 0 vR
  have hBlip : ∀ y z, |B z - B y| ≤ 1 * |z - y| :=
    abs_coleHopf_sub_le_of_lipschitz m hAm hAlip vR
  have hBm : Measurable B :=
    (lipschitzWith_toNNReal_of_abs_sub_le hBlip).continuous.measurable
  have hBg : HasLinearGrowth B := HasLinearGrowth.of_lipschitz hBlip
  have hDc : Continuous D :=
    continuous_integral_mul_coleHopfQ' hAc hAg m hA'c hA'g vR
  have hDb : ∀ y, |D y| ≤ 1 := fun y =>
    abs_integral_mul_coleHopfQ_le' hAg hAm m hA'm hA'b vR y
  have hDsqb : ∀ y, |D y ^ 2| ≤ 1 := by
    intro y
    rw [abs_pow]
    nlinarith [abs_nonneg (D y), hDb y]
  unfold coleHopfSplitMoment
  change |∫ z, D (x + z) ^ 2 * coleHopfQ m' vL B x z ∂gaussianReal 0 vL| ≤ 1
  exact abs_integral_mul_coleHopfQ_le' hBg hBm m' (hDc.pow 2).measurable hDsqb vL x

lemma coleHopfSplitMoment_nonneg (m m' : ℝ) (vR vL : ℝ≥0)
    (A A' : ℝ → ℝ) (x : ℝ) : 0 ≤ coleHopfSplitMoment m m' vR vL A A' x := by
  unfold coleHopfSplitMoment
  apply integral_nonneg
  intro z
  exact mul_nonneg (sq_nonneg _) (coleHopfQ_pos _ _ _ _ _).le

/-- The split moment is continuous in its spatial argument under the regularity used in the
Parisi recursion. -/
lemma continuous_coleHopfSplitMoment {m m' : ℝ} {vR vL : ℝ≥0}
    {A A' A'' : ℝ → ℝ} (hA : ∀ y, HasDerivAt A (A' y) y)
    (hA' : ∀ y, HasDerivAt A' (A'' y) y) (hA'b : ∀ y, |A' y| ≤ 1) :
    Continuous (coleHopfSplitMoment m m' vR vL A A') := by
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun y => (hA y).continuousAt
  have hA'c : Continuous A' := continuous_iff_continuousAt.2 fun y => (hA' y).continuousAt
  have hAg : HasLinearGrowth A := HasLinearGrowth.of_bounded_deriv hA hA'b
  have hA'g : HasExpGrowth A' := HasExpGrowth.of_bounded hA'b
  let B : ℝ → ℝ := coleHopf m vR A
  let D : ℝ → ℝ := fun y =>
    ∫ w, A' (y + w) * coleHopfQ m vR A y w ∂gaussianReal 0 vR
  have hBc : Continuous B :=
    by
      simpa [B, Function.comp_def] using
        (continuous_coleHopf hAc hAg m).comp
          (continuous_id.prodMk (continuous_const (y := (vR : ℝ))))
  have hAlip : ∀ x y, |A y - A x| ≤ 1 * |y - x| :=
    ProbabilityTheory.abs_sub_le_mul_abs_sub_of_hasDerivAt hA hA'b
  have hBlip : ∀ x y, |B y - B x| ≤ 1 * |y - x| :=
    abs_coleHopf_sub_le_of_lipschitz m hAc.measurable hAlip vR
  have hBg : HasLinearGrowth B := HasLinearGrowth.of_lipschitz hBlip
  have hDc : Continuous D :=
    continuous_integral_mul_coleHopfQ' hAc hAg m hA'c hA'g vR
  have hDb : ∀ y, |D y| ≤ 1 := fun y =>
    abs_integral_mul_coleHopfQ_le' hAg hAc.measurable m hA'c.measurable hA'b vR y
  have hDsqg : HasExpGrowth fun y => D y ^ 2 :=
    HasExpGrowth.of_bounded (C := 1) fun y => by
      rw [abs_pow]
      nlinarith [abs_nonneg (D y), hDb y]
  unfold coleHopfSplitMoment
  exact continuous_integral_mul_coleHopfQ' hBc hBg m' (hDc.pow 2) hDsqg vL

/-- The spatial derivative of one Cole-Hopf level is jointly continuous in its spatial
argument and variance, including variance zero. -/
lemma continuous_coleHopfDeriv_var {m : ℝ} {A A' : ℝ → ℝ}
    (hAc : Continuous A) (hAg : HasLinearGrowth A)
    (hA'c : Continuous A') (hA'g : HasExpGrowth A') :
    Continuous fun p : ℝ × ℝ =>
      ∫ z, A' (p.1 + z) * coleHopfQ m (Real.toNNReal p.2) A p.1 z
        ∂gaussianReal 0 (Real.toNNReal p.2) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [coleHopfQ_zero, mul_one]
    exact continuous_integral_comp_add_gaussianReal hA'c hA'g
  · let N : ℝ × ℝ → ℝ := fun p =>
      ∫ z, (A' * fun y => Real.exp (m * A y)) (p.1 + z)
        ∂gaussianReal 0 (Real.toNNReal p.2)
    let E : ℝ → ℝ := fun y => Real.exp (m * A y)
    let Z : ℝ × ℝ → ℝ := fun p =>
      ∫ z, E (p.1 + z)
        ∂gaussianReal 0 (Real.toNNReal p.2)
    have hNc : Continuous N := by
      apply continuous_integral_comp_add_gaussianReal
      · exact hA'c.mul (Real.continuous_exp.comp (continuous_const.mul hAc))
      · exact hA'g.mul (hAg.exp_mul m)
    have hZc : Continuous Z := by
      have hEc : Continuous E := by
        exact Real.continuous_exp.comp (continuous_const.mul hAc)
      have hEg : HasExpGrowth E := by
        exact hAg.exp_mul m
      exact continuous_integral_comp_add_gaussianReal hEc hEg
    have hZne : ∀ p, Z p ≠ 0 := fun p =>
      (integral_exp_mul_comp_add_pos hAg hAc.measurable m
        (Real.toNNReal p.2) p.1).ne'
    have hratio : Continuous fun p => N p / Z p := hNc.div hZc hZne
    apply hratio.congr
    intro p
    dsimp [N, Z, E]
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [coleHopfQ_eq hAg hAc.measurable hm]
    ring

/-- Cole-Hopf values converge uniformly in the spatial argument when their variances
converge. -/
lemma tendsto_uniform_coleHopf_of_tendsto_var
    {α : Type*} {l : Filter α} {v : α → ℝ≥0} {v₀ : ℝ≥0}
    {A : ℝ → ℝ} {L : ℝ} (hAm : Measurable A)
    (hAlip : ∀ x y, |A y - A x| ≤ L * |y - x|)
    (m : ℝ) (hv : Filter.Tendsto v l (nhds v₀)) :
    ∀ ε > 0, ∀ᶠ a in l, ∀ x,
      |coleHopf m (v a) A x - coleHopf m v₀ A x| < ε := by
  intro ε hε
  have hmod : ∀ᶠ t : ℝ in nhds 0,
      coleHopfModulus m L (Real.toNNReal t) < ε :=
    (tendsto_coleHopfModulus m L).eventually (Iio_mem_nhds hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hmod
  filter_upwards [hv.eventually (Metric.ball_mem_nhds v₀ hδ)] with a ha
  intro x
  rcases le_total v₀ (v a) with hle | hle
  · have hdiff : (((v a - v₀ : ℝ≥0) : ℝ)) ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      change dist (v a : ℝ) (v₀ : ℝ) < δ at ha
      have hleR : (v₀ : ℝ) ≤ (v a : ℝ) := mod_cast hle
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hleR)] at ha
      rw [sub_zero, NNReal.coe_sub hle, abs_of_nonneg (sub_nonneg.mpr hleR)]
      exact ha
    have hm := hball hdiff
    change coleHopfModulus m L (Real.toNNReal ((v a - v₀ : ℝ≥0) : ℝ)) < ε at hm
    rw [Real.toNNReal_coe] at hm
    exact (abs_coleHopf_sub_coleHopf_le hAm hAlip m hle x).trans_lt hm

  · rw [abs_sub_comm]
    have hdiff : (((v₀ - v a : ℝ≥0) : ℝ)) ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      change dist (v a : ℝ) (v₀ : ℝ) < δ at ha
      have hleR : (v a : ℝ) ≤ (v₀ : ℝ) := mod_cast hle
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hleR)] at ha
      rw [sub_zero, NNReal.coe_sub hle, abs_of_nonneg (sub_nonneg.mpr hleR)]
      linarith
    have hm := hball hdiff
    change coleHopfModulus m L (Real.toNNReal ((v₀ - v a : ℝ≥0) : ℝ)) < ε at hm
    rw [Real.toNNReal_coe] at hm
    exact (abs_coleHopf_sub_coleHopf_le hAm hAlip m hle x).trans_lt hm

/-- A fixed finite Cole-Hopf prefix does not enlarge a uniform terminal perturbation. -/
lemma abs_coleHopfIterate_sub_le_of_sup {j : ℕ} (ms : Fin j → ℝ)
    (vs : Fin j → ℝ≥0) {A B : ℝ → ℝ} {L ε : ℝ}
    (hAm : Measurable A) (hAlip : ∀ x y, |A y - A x| ≤ L * |y - x|)
    (hBm : Measurable B) (hBlip : ∀ x y, |B y - B x| ≤ L * |y - x|)
    (hAB : ∀ x, |A x - B x| ≤ ε) :
    ∀ x, |coleHopfIterate j ms vs A x - coleHopfIterate j ms vs B x| ≤ ε := by
  induction j with
  | zero => exact hAB
  | succ j ih =>
      rw [coleHopfIterate_succ, coleHopfIterate_succ]
      have hAiLip := abs_coleHopfIterate_sub_le j (Fin.tail ms) (Fin.tail vs) hAm hAlip
      have hBiLip := abs_coleHopfIterate_sub_le j (Fin.tail ms) (Fin.tail vs) hBm hBlip
      have hAiMeas :=
        (lipschitzWith_toNNReal_of_abs_sub_le hAiLip).continuous.measurable
      have hBiMeas :=
        (lipschitzWith_toNNReal_of_abs_sub_le hBiLip).continuous.measurable
      exact fun x => abs_coleHopf_sub_le_of_sup
        (HasLinearGrowth.of_lipschitz hAiLip) hAiMeas
        (HasLinearGrowth.of_lipschitz hBiLip) hBiMeas
        (ih (Fin.tail ms) (Fin.tail vs)) (ms 0) (vs 0) x

/-- A two-level variance split is uniformly continuous when both variances converge. -/
lemma tendsto_uniform_coleHopf_two_of_tendsto_var
    {α : Type*} {l : Filter α} {vL vR : α → ℝ≥0} {vL₀ vR₀ : ℝ≥0}
    {A : ℝ → ℝ} {L : ℝ} (hAm : Measurable A)
    (hAlip : ∀ x y, |A y - A x| ≤ L * |y - x|)
    (mL mR : ℝ) (hvL : Filter.Tendsto vL l (nhds vL₀))
    (hvR : Filter.Tendsto vR l (nhds vR₀)) :
    ∀ ε > 0, ∀ᶠ a in l, ∀ x,
      |coleHopf mL (vL a) (coleHopf mR (vR a) A) x -
        coleHopf mL vL₀ (coleHopf mR vR₀ A) x| < ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hinner := tendsto_uniform_coleHopf_of_tendsto_var hAm hAlip mR hvR
    (ε / 2) hhalf
  let B₀ : ℝ → ℝ := coleHopf mR vR₀ A
  have hB₀lip : ∀ x y, |B₀ y - B₀ x| ≤ L * |y - x| :=
    abs_coleHopf_sub_le_of_lipschitz mR hAm hAlip vR₀
  have hB₀m : Measurable B₀ :=
    (lipschitzWith_toNNReal_of_abs_sub_le hB₀lip).continuous.measurable
  have houter := tendsto_uniform_coleHopf_of_tendsto_var hB₀m hB₀lip mL hvL
    (ε / 2) hhalf
  filter_upwards [hinner, houter] with a hinner houter
  intro x
  let B : ℝ → ℝ := coleHopf mR (vR a) A
  have hBlip : ∀ y z, |B z - B y| ≤ L * |z - y| :=
    abs_coleHopf_sub_le_of_lipschitz mR hAm hAlip (vR a)
  have hBm : Measurable B :=
    (lipschitzWith_toNNReal_of_abs_sub_le hBlip).continuous.measurable
  have hfirst : |coleHopf mL (vL a) B x - coleHopf mL (vL a) B₀ x| ≤ ε / 2 :=
    abs_coleHopf_sub_le_of_sup
      (HasLinearGrowth.of_lipschitz hBlip) hBm
      (HasLinearGrowth.of_lipschitz hB₀lip) hB₀m
      (fun y => (hinner y).le) mL (vL a) x
  calc
    |coleHopf mL (vL a) (coleHopf mR (vR a) A) x -
        coleHopf mL vL₀ (coleHopf mR vR₀ A) x| ≤
        |coleHopf mL (vL a) B x - coleHopf mL (vL a) B₀ x| +
          |coleHopf mL (vL a) B₀ x - coleHopf mL vL₀ B₀ x| := by
            dsimp [B, B₀]
            exact abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hfirst (houter x)
    _ = ε := by ring

/-- With outer exponent zero, the split moment is jointly continuous in both variances and
the spatial argument.  In particular this covers the collapsed outer variance at `q₁ = 0`. -/
lemma continuous_coleHopfSplitMoment_zero_outer_var
    {m : ℝ} {A A' A'' : ℝ → ℝ}
    (hA : ∀ y, HasDerivAt A (A' y) y)
    (hA' : ∀ y, HasDerivAt A' (A'' y) y) {L : ℝ}
    (hA'b : ∀ y, |A' y| ≤ L) :
    Continuous fun p : (ℝ × ℝ) × ℝ =>
      coleHopfSplitMoment m 0 (Real.toNNReal p.1.1) (Real.toNNReal p.1.2)
        A A' p.2 := by
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun y => (hA y).continuousAt
  have hA'c : Continuous A' := continuous_iff_continuousAt.2 fun y => (hA' y).continuousAt
  have hAg : HasLinearGrowth A := HasLinearGrowth.of_bounded_deriv hA hA'b
  have hA'g : HasExpGrowth A' := HasExpGrowth.of_bounded hA'b
  let D : ℝ × ℝ → ℝ := fun p =>
    ∫ w, A' (p.1 + w) * coleHopfQ m (Real.toNNReal p.2) A p.1 w
      ∂gaussianReal 0 (Real.toNNReal p.2)
  have hDc : Continuous D := continuous_coleHopfDeriv_var hAc hAg hA'c hA'g
  have hDb : ∀ p, |D p| ≤ L := fun p =>
    abs_integral_mul_coleHopfQ_le' hAg hAc.measurable m hA'c.measurable hA'b
      (Real.toNNReal p.2) p.1
  let F : ((ℝ × ℝ) × ℝ) → ℝ → ℝ := fun p g =>
    D (p.2 + Real.sqrt (Real.toNNReal p.1.2) * g, p.1.1) ^ 2
  have hFc : ∀ g, Continuous fun p => F p g := by
    intro g
    have hs : Continuous fun p : (ℝ × ℝ) × ℝ =>
        Real.sqrt (Real.toNNReal p.1.2 : ℝ) :=
      Real.continuous_sqrt.comp (NNReal.continuous_coe.comp
        (continuous_real_toNNReal.comp (continuous_snd.comp continuous_fst)))
    have hp : Continuous fun p : (ℝ × ℝ) × ℝ =>
        (p.2 + Real.sqrt (Real.toNNReal p.1.2) * g, p.1.1) :=
      (continuous_snd.add (hs.mul (continuous_const (y := g)))).prodMk
        (continuous_fst.comp continuous_fst)
    exact (hDc.comp hp).pow 2
  have hFgc : ∀ p, Continuous (F p) := by
    intro p
    exact (hDc.comp ((continuous_const.add
      (continuous_const.mul continuous_id)).prodMk continuous_const)).pow 2
  have hFb : ∀ p g, ‖F p g‖ ≤ L ^ 2 := by
    intro p g
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hDb _) 2
  have hFcont : Continuous fun p => ∫ g, F p g ∂gaussianReal 0 1 := by
    rw [continuous_iff_continuousAt]
    intro p
    exact continuousAt_of_dominated
      (Filter.Eventually.of_forall fun q => (hFgc q).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun q =>
        Filter.Eventually.of_forall fun g => hFb q g)
      (integrable_const (μ := gaussianReal 0 1) (L ^ 2))
      (Filter.Eventually.of_forall fun g => (hFc g).continuousAt)
  apply hFcont.congr
  intro p
  unfold coleHopfSplitMoment
  simp only [coleHopfQ_zero, mul_one]
  have hm : AEStronglyMeasurable
      (fun z => D (p.2 + z, p.1.1) ^ 2)
      (gaussianReal 0 (Real.toNNReal p.1.2)) :=
    ((hDc.comp (continuous_const.add continuous_id |>.prodMk continuous_const)).pow 2).measurable
      |>.aestronglyMeasurable
  rw [integral_gaussianReal_eq_integral_sqrt_mul _ hm]

/-- A pointwise strict upper bound remains strict after averaging by a probability measure. -/
lemma integral_lt_one_of_measurable_of_lt {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}
    (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ 1) (hflt : ∀ x, f x < 1) :
    ∫ x, f x ∂μ < 1 := by
  have hfi : Integrable f μ :=
    Integrable.of_bound hfm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hfb x)
  have hdiffi : Integrable (fun x => 1 - f x) μ := (integrable_const 1).sub hfi
  have hdiffpos : 0 < ∫ x, 1 - f x ∂μ := by
    rw [integral_pos_iff_support_of_nonneg
      (fun x => sub_nonneg.mpr (hflt x).le) hdiffi]
    have hsupp : Function.support (fun x => 1 - f x) = Set.univ := by
      ext x
      simp only [Function.mem_support, mem_univ, iff_true]
      exact ne_of_gt (sub_pos.mpr (hflt x))
    rw [hsupp, measure_univ]
    norm_num
  rw [integral_sub (integrable_const 1) hfi, integral_const, probReal_univ, one_smul] at hdiffpos
  linarith

/-- A bounded observable averaged by a Gaussian cascade tilt is measurable in the common
spatial translation parameter. -/
lemma measurable_integral_cascadeTiltMeasure_comp_add_sum {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) {G f : ℝ → ℝ} {L : ℝ}
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (hGm : Measurable G)
    (hGlip : ∀ x y, |G y - G x| ≤ L * |y - x|) (hfm : Measurable f) :
    Measurable fun x =>
      ∫ zs, f (x + ∑ p, zs p)
        ∂cascadeTiltMeasure j ms (fun p => gaussianReal 0 (vs p))
          (fun zs => ENNReal.ofReal (Real.exp (G (x + ∑ p, zs p)))) := by
  let μs : Fin j → Measure ℝ := fun p => gaussianReal 0 (vs p)
  let Gs : ℝ → (Fin j → ℝ) → ℝ≥0∞ := fun x zs =>
    ENNReal.ofReal (Real.exp (G (x + ∑ p, zs p)))
  have hsum : Measurable fun q : ℝ × (Fin j → ℝ) => q.1 + ∑ p, q.2 p :=
    measurable_fst.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p |>.comp measurable_snd)
  have hGsjoint : Measurable (Function.uncurry Gs) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hGm.comp hsum))
  have hdens : Measurable fun q : ℝ × (Fin j → ℝ) =>
      cascadeTiltDensity j ms μs (Gs q.1) q.2 :=
    measurable_cascadeTiltDensity_prod j ms μs hGsjoint
  have hjoint : Measurable fun q : ℝ × (Fin j → ℝ) =>
      (cascadeTiltDensity j ms μs (Gs q.1) q.2).toReal *
        f (q.1 + ∑ p, q.2 p) :=
    hdens.ennreal_toReal.mul (hfm.comp hsum)
  have hrhs : Measurable fun x =>
      ∫ zs, (cascadeTiltDensity j ms μs (Gs x) zs).toReal *
        f (x + ∑ p, zs p) ∂Measure.pi μs :=
    hjoint.stronglyMeasurable.integral_prod_right'.measurable
  have heq : (fun x =>
      ∫ zs, f (x + ∑ p, zs p)
        ∂cascadeTiltMeasure j ms (fun p => gaussianReal 0 (vs p))
          (fun zs => ENNReal.ofReal (Real.exp (G (x + ∑ p, zs p))))) =
      fun x => ∫ zs, (cascadeTiltDensity j ms μs (Gs x) zs).toReal *
        f (x + ∑ p, zs p) ∂Measure.pi μs := by
    funext x
    change (∫ zs, f (x + ∑ p, zs p) ∂cascadeTiltMeasure j ms μs (Gs x)) = _
    have hGx : Measurable (Gs x) := hGsjoint.comp (measurable_const.prodMk measurable_id)
    have hfin : ∫⁻ zs, Gs x zs ∂Measure.pi μs ≠ ∞ := by
      simpa [Gs, μs] using
        (lintegral_ofReal_exp_comp_add_sum_pi_gaussianReal_ne_top vs hGlip x)
    simpa only [smul_eq_mul] using
      (integral_cascadeTiltMeasure j ms μs hGx
        (fun zs => by simp only [Gs]; exact ENNReal.ofReal_pos.2 (Real.exp_pos _))
        hpos hle hfin (fun zs => f (x + ∑ p, zs p)))
  rw [heq]
  exact hrhs

/-- When the inner variance is zero and the terminal derivative is strictly bounded by one,
the split moment is strictly below one. -/
lemma coleHopfSplitMoment_lt_one_of_zero_right {m m' : ℝ} {vL : ℝ≥0}
    {A A' A'' : ℝ → ℝ} (hA : ∀ y, HasDerivAt A (A' y) y)
    (hA' : ∀ y, HasDerivAt A' (A'' y) y) (hA'lt : ∀ y, |A' y| < 1) (x : ℝ) :
    coleHopfSplitMoment m m' 0 vL A A' x < 1 := by
  have hAm : Measurable A := measurable_of_hasDerivAt hA
  have hA'm : Measurable A' := measurable_of_hasDerivAt hA'
  have hA'b : ∀ y, |A' y| ≤ 1 := fun y => (hA'lt y).le
  have hAg : HasLinearGrowth A := HasLinearGrowth.of_bounded_deriv hA hA'b
  have hsq_lt : ∀ y, A' y ^ 2 < 1 := by
    intro y
    have hpos : 0 < (1 - |A' y|) * (1 + |A' y|) :=
      mul_pos (sub_pos.mpr (hA'lt y)) (by positivity)
    nlinarith [sq_abs (A' y)]
  have hA'sqg : HasExpGrowth fun y => A' y ^ 2 :=
    HasExpGrowth.of_bounded (C := 1) fun y => by
      rw [abs_pow]
      nlinarith [abs_nonneg (A' y), hA'b y]
  have hA'sqm : Measurable fun y => A' y ^ 2 := hA'm.pow_const 2
  have hQi : Integrable (coleHopfQ m' vL A x) (gaussianReal 0 vL) := by
    rcases eq_or_ne m' 0 with rfl | hm'
    · convert (integrable_const (μ := gaussianReal 0 vL) (1 : ℝ)) using 1
      funext z
      exact coleHopfQ_zero vL A x z
    · exact integrable_coleHopfQ hAg hAm hm' vL x
  have hQone : ∫ z, coleHopfQ m' vL A x z ∂gaussianReal 0 vL = 1 := by
    rcases eq_or_ne m' 0 with rfl | hm'
    · simp
    · exact integral_coleHopfQ hAg hAm hm' vL x
  have hsqi : Integrable (fun z => A' (x + z) ^ 2 * coleHopfQ m' vL A x z)
      (gaussianReal 0 vL) := by
    rcases eq_or_ne m' 0 with rfl | hm'
    · simp only [coleHopfQ_zero, mul_one]
      exact (hA'sqg.comp_add_const x).integrable_gaussianReal
        (hA'sqm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    · exact integrable_mul_coleHopfQ hAg hAm hm' hA'sqg hA'sqm vL x
  have hdiffi : Integrable
      (fun z => (1 - A' (x + z) ^ 2) * coleHopfQ m' vL A x z)
      (gaussianReal 0 vL) := by
    convert hQi.sub hsqi using 1
    funext z
    simp only [Pi.sub_apply]
    ring
  have hdiffpos : 0 < ∫ z, (1 - A' (x + z) ^ 2) * coleHopfQ m' vL A x z
      ∂gaussianReal 0 vL := by
    rw [integral_pos_iff_support_of_nonneg (fun z => by
        exact mul_nonneg (le_of_lt (sub_pos.mpr (hsq_lt (x + z))))
          (coleHopfQ_pos _ _ _ _ _).le) hdiffi]
    have hsupp : Function.support
        (fun z => (1 - A' (x + z) ^ 2) * coleHopfQ m' vL A x z) = Set.univ := by
      ext z
      simp only [Function.mem_support, mem_univ, iff_true]
      exact ne_of_gt (mul_pos
        (sub_pos.mpr (hsq_lt (x + z)))
        (coleHopfQ_pos _ _ _ _ _))
    rw [hsupp, measure_univ]
    norm_num
  have hsplit : coleHopfSplitMoment m m' 0 vL A A' x =
      ∫ z, A' (x + z) ^ 2 * coleHopfQ m' vL A x z ∂gaussianReal 0 vL := by
    unfold coleHopfSplitMoment
    simp only [gaussianReal_zero_var, integral_dirac, add_zero]
    have hBzero : coleHopf m 0 A = A := by
      funext y
      exact coleHopf_zero_var m A y
    rw [hBzero]
    apply integral_congr_ae
    filter_upwards [] with z
    simp [coleHopfQ]
  rw [hsplit]
  have heq : (∫ z, (1 - A' (x + z) ^ 2) * coleHopfQ m' vL A x z
      ∂gaussianReal 0 vL) = 1 -
        ∫ z, A' (x + z) ^ 2 * coleHopfQ m' vL A x z ∂gaussianReal 0 vL := by
    calc
      (∫ z, (1 - A' (x + z) ^ 2) * coleHopfQ m' vL A x z
          ∂gaussianReal 0 vL) =
          (∫ z, coleHopfQ m' vL A x z ∂gaussianReal 0 vL) -
            ∫ z, A' (x + z) ^ 2 * coleHopfQ m' vL A x z
              ∂gaussianReal 0 vL := by
            rw [← integral_sub hQi hsqi]
            apply integral_congr_ae
            filter_upwards [] with z
            ring
      _ = 1 - ∫ z, A' (x + z) ^ 2 * coleHopfQ m' vL A x z
          ∂gaussianReal 0 vL := by rw [hQone]
  linarith

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

/-! ### The concrete suffix functions `$A_{r+1}$` -/

/-- The one-site terminal function with external field `h`. -/
def parisiLogCoshTerminal (h x : ℝ) : ℝ := Real.log (Real.cosh (h + x))

/-- Its first derivative. -/
def parisiLogCoshTerminalDeriv (h x : ℝ) : ℝ := Real.tanh (h + x)

/-- Its second derivative. -/
def parisiLogCoshTerminalDeriv2 (h x : ℝ) : ℝ := 1 - Real.tanh (h + x) ^ 2

lemma hasDerivAt_parisiLogCoshTerminal (h x : ℝ) :
    HasDerivAt (parisiLogCoshTerminal h) (parisiLogCoshTerminalDeriv h x) x := by
  have hadd : HasDerivAt (fun y : ℝ => h + y) 1 x :=
    by simpa using (hasDerivAt_id x).const_add h
  change HasDerivAt (fun y : ℝ => Real.log (Real.cosh (h + y))) (Real.tanh (h + x)) x
  simpa only [Function.comp_def, mul_one] using
    (Real.hasDerivAt_log_cosh (h + x)).comp x hadd

lemma hasDerivAt_parisiLogCoshTerminalDeriv (h x : ℝ) :
    HasDerivAt (parisiLogCoshTerminalDeriv h) (parisiLogCoshTerminalDeriv2 h x) x := by
  have hadd : HasDerivAt (fun y : ℝ => h + y) 1 x :=
    by simpa using (hasDerivAt_id x).const_add h
  change HasDerivAt (fun y : ℝ => Real.tanh (h + y))
    (1 - Real.tanh (h + x) ^ 2) x
  simpa only [Function.comp_def, mul_one] using
    (Real.hasDerivAt_tanh (h + x)).comp x hadd

lemma continuous_parisiLogCoshTerminalDeriv2 (h : ℝ) :
    Continuous (parisiLogCoshTerminalDeriv2 h) := by
  unfold parisiLogCoshTerminalDeriv2
  have htanh : Continuous Real.tanh :=
    continuous_iff_continuousAt.2 fun x => (Real.hasDerivAt_tanh x).continuousAt
  exact continuous_const.sub ((htanh.comp (continuous_const.add continuous_id)).pow 2)

lemma abs_parisiLogCoshTerminalDeriv_lt_one (h x : ℝ) :
    |parisiLogCoshTerminalDeriv h x| < 1 := by
  simpa [parisiLogCoshTerminalDeriv] using Real.abs_tanh_lt_one (h + x)

lemma abs_parisiLogCoshTerminalDeriv2_le_one (h x : ℝ) :
    |parisiLogCoshTerminalDeriv2 h x| ≤ 1 := by
  have hsquare : Real.tanh (h + x) ^ 2 < 1 := Real.tanh_sq_lt_one (h + x)
  have hnonneg : 0 ≤ 1 - Real.tanh (h + x) ^ 2 := by linarith
  rw [parisiLogCoshTerminalDeriv2, abs_of_nonneg hnonneg]
  nlinarith [sq_nonneg (Real.tanh (h + x))]

/-- The terminal Cole--Hopf level with exponent one is absorbed exactly. -/
lemma coleHopf_one_parisiLogCoshTerminal (h : ℝ) (v : ℝ≥0) (x : ℝ) :
    coleHopf 1 v (parisiLogCoshTerminal h) x =
      (v : ℝ) / 2 + parisiLogCoshTerminal h x := by
  rw [coleHopf_of_ne one_ne_zero]
  simp only [one_div, one_mul]
  have hint :
      (∫ z, Real.exp (parisiLogCoshTerminal h (x + z)) ∂gaussianReal 0 v) =
        Real.cosh (h + x) * Real.exp ((v : ℝ) / 2) := by
    calc
      (∫ z, Real.exp (parisiLogCoshTerminal h (x + z)) ∂gaussianReal 0 v) =
          ∫ z, Real.cosh (h + x + z) ∂gaussianReal 0 v := by
            apply integral_congr_ae
            filter_upwards [] with z
            rw [parisiLogCoshTerminal, Real.exp_log (Real.cosh_pos _)]
            congr 1
            ring
      _ = Real.cosh (h + x) * Real.exp ((v : ℝ) / 2) :=
        integral_cosh_add_gaussianReal (h + x) v
  rw [hint, Real.log_mul (Real.cosh_pos _).ne' (Real.exp_ne_zero _), Real.log_exp]
  rw [parisiLogCoshTerminal]
  ring

/-- The one-site terminal function is one-Lipschitz. -/
lemma abs_parisiLogCoshTerminal_sub_le (h x y : ℝ) :
    |parisiLogCoshTerminal h y - parisiLogCoshTerminal h x| ≤ |y - x| := by
  simpa only [one_mul] using ProbabilityTheory.abs_sub_le_mul_abs_sub_of_hasDerivAt
    (hasDerivAt_parisiLogCoshTerminal h)
    (fun z => (abs_parisiLogCoshTerminalDeriv_lt_one h z).le) x y

/-- The zero-field Gaussian recursion is even in its spatial argument. -/
lemma logCoshRec_neg_local {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (a : ℝ) :
    logCoshRec j ms vs (-a) = logCoshRec j ms vs a := by
  unfold logCoshRec parisiRec
  have hμ : (fun p : Fin j => (gaussianReal 0 (vs p)).map (fun x : ℝ => -x)) =
      fun p => gaussianReal 0 (vs p) := funext fun p => by
    rw [gaussianReal_map_neg, neg_zero]
  have hG : Measurable fun y : Fin j → ℝ =>
      ENNReal.ofReal (Real.exp (Real.log (Real.cosh (a + ∑ p, y p)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Real.measurable_log.comp
      (Real.continuous_cosh.measurable.comp (measurable_const.add
        (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)))))
  have hfun : (fun y : Fin j → ℝ =>
        ENNReal.ofReal (Real.exp (Real.log (Real.cosh (-a + ∑ p, y p))))) =
      fun zs => ENNReal.ofReal (Real.exp (Real.log (Real.cosh (a + ∑ p, -zs p)))) := by
    funext y
    rw [show a + ∑ p, -y p = -(-a + ∑ p, y p) by
      rw [Finset.sum_neg_distrib]
      ring, Real.cosh_neg]
  conv_rhs => rw [← hμ]
  rw [cascadeRec_map j ms _ (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg) hG, hfun]

lemma logCoshRec_eq_coleHopfIterate_terminal_zero {j : ℕ} (ms : Fin j → ℝ)
    (vs : Fin j → ℝ≥0) (hpos : ∀ i, 0 < ms i) (a : ℝ) :
    logCoshRec j ms vs a =
      coleHopfIterate j ms vs (parisiLogCoshTerminal 0) a := by
  unfold logCoshRec
  simpa [parisiLogCoshTerminal] using parisiRec_gaussian_comp_add_sum (L := 1) ms vs hpos
    (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0))
    (fun x y => by simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0 x y) a

/-- Translating the external field translates the spatial derivative of the recursion. -/
theorem coleHopfIterateDeriv_parisiLogCoshTerminal_translate {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (hpos : ∀ i, 0 < ms i) (h : ℝ) :
    coleHopfIterateDeriv j ms vs (parisiLogCoshTerminal h)
        (parisiLogCoshTerminalDeriv h) 0 =
      coleHopfIterateDeriv j ms vs (parisiLogCoshTerminal 0)
        (parisiLogCoshTerminalDeriv 0) h := by
  let B : ℝ → ℝ := coleHopfIterate j ms vs (parisiLogCoshTerminal 0)
  let B' : ℝ → ℝ := coleHopfIterateDeriv j ms vs (parisiLogCoshTerminal 0)
    (parisiLogCoshTerminalDeriv 0)
  obtain ⟨hB, C, hB', hB''c, hB'b, hB''b⟩ :=
    coleHopfIterate_deriv_regular ms vs
      (hasDerivAt_parisiLogCoshTerminal 0)
      (hasDerivAt_parisiLogCoshTerminalDeriv 0)
      (continuous_parisiLogCoshTerminalDeriv2 0)
      (fun x => (abs_parisiLogCoshTerminalDeriv_lt_one 0 x).le)
      (abs_parisiLogCoshTerminalDeriv2_le_one 0) hpos
  obtain ⟨hAh, C', hAh', hAh''c, hAh'b, hAh''b⟩ :=
    coleHopfIterate_deriv_regular ms vs
      (hasDerivAt_parisiLogCoshTerminal h)
      (hasDerivAt_parisiLogCoshTerminalDeriv h)
      (continuous_parisiLogCoshTerminalDeriv2 h)
      (fun x => (abs_parisiLogCoshTerminalDeriv_lt_one h x).le)
      (abs_parisiLogCoshTerminalDeriv2_le_one h) hpos
  have htranslate : coleHopfIterate j ms vs (parisiLogCoshTerminal h) =
      fun x => B (h + x) := by
    funext x
    calc
      coleHopfIterate j ms vs (parisiLogCoshTerminal h) x =
          parisiRec j ms (fun p => gaussianReal 0 (vs p))
            (fun zs => parisiLogCoshTerminal h (x + ∑ p, zs p)) :=
        (parisiRec_gaussian_comp_add_sum (L := 1) ms vs hpos
          (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal h))
          (fun y z => by simpa only [one_mul] using
            abs_parisiLogCoshTerminal_sub_le h y z) x).symm
      _ = parisiRec j ms (fun p => gaussianReal 0 (vs p))
            (fun zs => parisiLogCoshTerminal 0 (h + x + ∑ p, zs p)) := by
        congr 1
        funext zs
        unfold parisiLogCoshTerminal
        apply congrArg Real.log
        apply congrArg Real.cosh
        ring
      _ = coleHopfIterate j ms vs (parisiLogCoshTerminal 0) (h + x) :=
        parisiRec_gaussian_comp_add_sum (L := 1) ms vs hpos
          (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0))
          (fun y z => by simpa only [one_mul] using
            abs_parisiLogCoshTerminal_sub_le 0 y z) (h + x)
      _ = B (h + x) := rfl
  have hadd : HasDerivAt (fun x : ℝ => h + x) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add h
  have hrightRaw := (hB (h + 0)).comp 0 hadd
  have hfunadd :
      (coleHopfIterate j ms vs (parisiLogCoshTerminal 0) ∘ HAdd.hAdd h) =
        fun x : ℝ => B (h + x) := by rfl
  rw [hfunadd] at hrightRaw
  have hdraw :
      coleHopfIterateDeriv j ms vs (parisiLogCoshTerminal 0)
          (parisiLogCoshTerminalDeriv 0) (h + 0) * 1 = B' h := by
    simp [B']
  rw [hdraw, ← htranslate] at hrightRaw
  exact HasDerivAt.unique (hAh 0) hrightRaw

/-- The spatial derivative of the concrete recursion is nonzero when the external field is
nonzero. -/
theorem coleHopfIterateDeriv_parisiLogCoshTerminal_ne_zero {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    {h : ℝ} (hh : h ≠ 0) :
    coleHopfIterateDeriv j ms vs (parisiLogCoshTerminal h)
      (parisiLogCoshTerminalDeriv h) 0 ≠ 0 := by
  let B : ℝ → ℝ := coleHopfIterate j ms vs (parisiLogCoshTerminal 0)
  let B' : ℝ → ℝ := coleHopfIterateDeriv j ms vs (parisiLogCoshTerminal 0)
    (parisiLogCoshTerminalDeriv 0)
  let B'' : ℝ → ℝ := coleHopfIterateDeriv2 j ms vs (parisiLogCoshTerminal 0)
    (parisiLogCoshTerminalDeriv 0) (parisiLogCoshTerminalDeriv2 0)
  obtain ⟨hB, C, hB', hB''c, hB'b, hB''b⟩ :=
    coleHopfIterate_deriv_regular ms vs
      (hasDerivAt_parisiLogCoshTerminal 0)
      (hasDerivAt_parisiLogCoshTerminalDeriv 0)
      (continuous_parisiLogCoshTerminalDeriv2 0)
      (fun x => (abs_parisiLogCoshTerminalDeriv_lt_one 0 x).le)
      (abs_parisiLogCoshTerminalDeriv2_le_one 0) hpos
  have hterminalPos : ∀ x, 0 < parisiLogCoshTerminalDeriv2 0 x := by
    intro x
    simpa [parisiLogCoshTerminalDeriv2] using
      (sub_pos.mpr (Real.tanh_sq_lt_one x))
  have hB''pos : ∀ x, 0 < B'' x :=
    coleHopfIterateDeriv2_pos ms vs
      (hasDerivAt_parisiLogCoshTerminal 0)
      (hasDerivAt_parisiLogCoshTerminalDeriv 0)
      (continuous_parisiLogCoshTerminalDeriv2 0)
      (fun x => (abs_parisiLogCoshTerminalDeriv_lt_one 0 x).le)
      (abs_parisiLogCoshTerminalDeriv2_le_one 0) hterminalPos hpos
  have hBsm : StrictMono B' := strictMono_of_deriv_pos fun x => by
    rw [(hB' x).deriv]
    exact hB''pos x
  have hBeven : Function.Even B := by
    intro a
    dsimp [B]
    rw [← logCoshRec_eq_coleHopfIterate_terminal_zero ms vs hpos,
      ← logCoshRec_eq_coleHopfIterate_terminal_zero ms vs hpos]
    exact logCoshRec_neg_local ms vs a
  have hBzero : B' 0 = 0 := by
    have hcomp : HasDerivAt (fun x => B (-x)) (-B' 0) 0 := by
      have hneg := (hasDerivAt_id (0 : ℝ)).neg
      change HasDerivAt (fun x : ℝ => -x) (-1) 0 at hneg
      have hraw := (hB (-0)).comp 0 hneg
      have hfunneg :
          (coleHopfIterate j ms vs (parisiLogCoshTerminal 0) ∘ Neg.neg) =
            fun x : ℝ => B (-x) := by rfl
      rw [hfunneg] at hraw
      have hdraw :
          coleHopfIterateDeriv j ms vs (parisiLogCoshTerminal 0)
              (parisiLogCoshTerminalDeriv 0) (-0) * (-1) = -B' 0 := by
        simp [B']
      rw [hdraw] at hraw
      exact hraw
    have hfun : (fun x => B (-x)) = B := funext hBeven
    rw [hfun] at hcomp
    have hu := HasDerivAt.unique hcomp (hB 0)
    linarith
  have hB'h : B' h ≠ 0 := by
    rcases lt_or_gt_of_ne hh with hhneg | hhpos
    · have hlt := hBsm hhneg
      rw [hBzero] at hlt
      exact ne_of_lt hlt
    · have hlt := hBsm hhpos
      rw [hBzero] at hlt
      exact ne_of_gt hlt
  obtain ⟨hAh, C', hAh', hAh''c, hAh'b, hAh''b⟩ :=
    coleHopfIterate_deriv_regular ms vs
      (hasDerivAt_parisiLogCoshTerminal h)
      (hasDerivAt_parisiLogCoshTerminalDeriv h)
      (continuous_parisiLogCoshTerminalDeriv2 h)
      (fun x => (abs_parisiLogCoshTerminalDeriv_lt_one h x).le)
      (abs_parisiLogCoshTerminalDeriv2_le_one h) hpos
  have htranslate : coleHopfIterate j ms vs (parisiLogCoshTerminal h) =
      fun x => B (h + x) := by
    funext x
    calc
      coleHopfIterate j ms vs (parisiLogCoshTerminal h) x =
          parisiRec j ms (fun p => gaussianReal 0 (vs p))
            (fun zs => parisiLogCoshTerminal h (x + ∑ p, zs p)) :=
        (parisiRec_gaussian_comp_add_sum (L := 1) ms vs hpos
          (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal h))
          (fun y z => by simpa only [one_mul] using
            abs_parisiLogCoshTerminal_sub_le h y z) x).symm
      _ = parisiRec j ms (fun p => gaussianReal 0 (vs p))
            (fun zs => parisiLogCoshTerminal 0 (h + x + ∑ p, zs p)) := by
        congr 1
        funext zs
        unfold parisiLogCoshTerminal
        apply congrArg Real.log
        apply congrArg Real.cosh
        ring
      _ = coleHopfIterate j ms vs (parisiLogCoshTerminal 0) (h + x) :=
        parisiRec_gaussian_comp_add_sum (L := 1) ms vs hpos
          (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0))
          (fun y z => by simpa only [one_mul] using
            abs_parisiLogCoshTerminal_sub_le 0 y z) (h + x)
      _ = B (h + x) := rfl
  have hright : HasDerivAt (fun x => B (h + x)) (B' h) 0 := by
    have hadd : HasDerivAt (fun x : ℝ => h + x) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add h
    have hraw := (hB (h + 0)).comp 0 hadd
    have hfunadd :
        (coleHopfIterate j ms vs (parisiLogCoshTerminal 0) ∘ HAdd.hAdd h) =
          fun x : ℝ => B (h + x) := by rfl
    rw [hfunadd] at hraw
    have hdraw :
        coleHopfIterateDeriv j ms vs (parisiLogCoshTerminal 0)
            (parisiLogCoshTerminalDeriv 0) (h + 0) * 1 = B' h := by
      simp [B']
    rw [hdraw] at hraw
    exact hraw
  rw [← htranslate] at hright
  have heq := HasDerivAt.unique (hAh 0) hright
  rwa [heq]

/-- The masses of all Cole-Hopf levels in `parisiRecGauss`. -/
def parisiLevelMasses {k : ℕ} (ms : Fin k → ℝ) : Fin (k + 1) → ℝ :=
  Fin.snoc ms 1

@[simp] lemma parisiLevelMasses_apply {k : ℕ} (ms : Fin k → ℝ) (p : Fin (k + 1)) :
    parisiLevelMasses ms p = mExt ms (p.val + 1) := by
  refine Fin.lastCases ?_ (fun i => ?_) p
  · simp [parisiLevelMasses, mExt_eq_one_of_le]
  · simp [parisiLevelMasses, mExt_val_succ]

/-- The variances of all Cole-Hopf levels in `parisiRecGauss`. -/
def parisiLevelVars (ξ : ℝ → ℝ) {k : ℕ} (qs : Fin (k + 1) → ℝ) :
    Fin (k + 1) → ℝ≥0 := fun p => parisiVar ξ qs (p.val + 1)

/-- The Gaussian Parisi recursion is the concrete Cole-Hopf iterate used below. -/
theorem parisiRecGauss_eq_coleHopfIterate {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (z₀ : ℝ) :
    parisiRecGauss ξ ms qs (parisiLogCoshTerminal h) z₀ =
      coleHopfIterate (k + 1) (parisiLevelMasses ms) (parisiLevelVars ξ qs)
        (parisiLogCoshTerminal h) z₀ := by
  unfold parisiRecGauss parisiMarks parisiLevelMasses parisiLevelVars
  apply parisiRec_gaussian_comp_add_sum (L := 1)
  · intro p
    refine Fin.lastCases ?_ (fun i => ?_) p
    · simp
    · simpa using hm.2.1 i
  · exact measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal h)
  · intro x y
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le h x y

/-- `parisiX₀` is the outer Gaussian average of the concrete Cole-Hopf iterate. -/
theorem parisiX₀_eq_integral_coleHopfIterate {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) :
    parisiX₀ ξ ms qs (parisiLogCoshTerminal h) =
      ∫ z₀, coleHopfIterate (k + 1) (parisiLevelMasses ms) (parisiLevelVars ξ qs)
        (parisiLogCoshTerminal h) z₀ ∂gaussianReal 0 (parisiVar ξ qs 0) := by
  unfold parisiX₀
  congr 1
  funext z₀
  exact parisiRecGauss_eq_coleHopfIterate qs hm z₀

/-- The positive-exponent levels preceding the two levels adjacent to `r`. -/
def parisiQPrefixMasses {k : ℕ} (ms : Fin k → ℝ) (r : Fin (k + 1)) :
    Fin (r.val - 1) → ℝ := fun p => mExt ms (p.val + 1)

/-- The unchanged variances preceding the two levels adjacent to `r`. -/
def parisiQPrefixVars (ξ : ℝ → ℝ) {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) : Fin (r.val - 1) → ℝ≥0 :=
  fun p => parisiVar ξ qs (p.val + 1)

/-- The masses strictly after the two levels adjacent to the coordinate represented by `r`. -/
def parisiQSuffixMasses {k : ℕ} (ms : Fin k → ℝ) (r : Fin (k + 1)) :
    Fin (k - r.val) → ℝ := fun p => mExt ms (r.val + p.val + 2)

/-- The variances strictly after the two levels adjacent to the coordinate represented by `r`. -/
def parisiQSuffixVars (ξ : ℝ → ℝ) {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) : Fin (k - r.val) → ℝ≥0 :=
  fun p => parisiVar ξ qs (r.val + p.val + 2)

/-- Talagrand's `$A_{r+2}$`, namely the part of the recursion strictly inside the two levels
whose variance split changes when the free coordinate represented by `r` moves. -/
noncomputable def parisiQSuffix (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) : ℝ → ℝ :=
  coleHopfIterate (k - r.val) (parisiQSuffixMasses ms r) (parisiQSuffixVars ξ qs r)
    (parisiLogCoshTerminal h)

/-- The canonical first derivative of `parisiQSuffix`. -/
noncomputable def parisiQSuffixDeriv (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) : ℝ → ℝ :=
  coleHopfIterateDeriv (k - r.val) (parisiQSuffixMasses ms r) (parisiQSuffixVars ξ qs r)
    (parisiLogCoshTerminal h) (parisiLogCoshTerminalDeriv h)

/-- The canonical second derivative of `parisiQSuffix`. -/
noncomputable def parisiQSuffixDeriv2 (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) : ℝ → ℝ :=
  coleHopfIterateDeriv2 (k - r.val) (parisiQSuffixMasses ms r) (parisiQSuffixVars ξ qs r)
    (parisiLogCoshTerminal h) (parisiLogCoshTerminalDeriv h)
    (parisiLogCoshTerminalDeriv2 h)

lemma parisiQSuffixVars_qUpdate (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : ℝ) :
    parisiQSuffixVars ξ (qUpdate qs r u) r = parisiQSuffixVars ξ qs r := by
  funext p
  unfold parisiQSuffixVars
  rw [parisiVar_qUpdate_after]
  omega

lemma parisiQSuffix_qUpdate (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : ℝ) :
    parisiQSuffix ξ h ms (qUpdate qs r u) r = parisiQSuffix ξ h ms qs r := by
  unfold parisiQSuffix
  rw [parisiQSuffixVars_qUpdate]

lemma parisiQSuffixDeriv_qUpdate (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : ℝ) :
    parisiQSuffixDeriv ξ h ms (qUpdate qs r u) r =
      parisiQSuffixDeriv ξ h ms qs r := by
  unfold parisiQSuffixDeriv
  rw [parisiQSuffixVars_qUpdate]

lemma parisiQSuffix_translate (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (x : ℝ) :
    parisiQSuffix ξ h ms qs r x = parisiQSuffix ξ 0 ms qs r (h + x) := by
  have hterminal : parisiLogCoshTerminal h = fun y => parisiLogCoshTerminal 0 (h + y) := by
    funext y
    unfold parisiLogCoshTerminal
    apply congrArg Real.log
    apply congrArg Real.cosh
    ring
  unfold parisiQSuffix
  rw [hterminal]
  exact coleHopfIterate_translate _ _ _ h x

lemma parisiQSuffixDeriv_translate (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (x : ℝ) :
    parisiQSuffixDeriv ξ h ms qs r x = parisiQSuffixDeriv ξ 0 ms qs r (h + x) := by
  have hterminal : parisiLogCoshTerminal h = fun y => parisiLogCoshTerminal 0 (h + y) := by
    funext y
    unfold parisiLogCoshTerminal
    apply congrArg Real.log
    apply congrArg Real.cosh
    ring
  have hterminal' : parisiLogCoshTerminalDeriv h =
      fun y => parisiLogCoshTerminalDeriv 0 (h + y) := by
    funext y
    unfold parisiLogCoshTerminalDeriv
    apply congrArg Real.tanh
    ring
  unfold parisiQSuffixDeriv
  rw [hterminal, hterminal']
  exact coleHopfIterateDeriv_translate _ _ _ _ h x

/-- The actual recursive suffix has the regularity and uniform first-derivative bound required
by the split derivative theorem. -/
theorem parisiQSuffix_deriv_regular {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hm : ParisiMAdmissible ms) :
    (∀ x, HasDerivAt (parisiQSuffix ξ h ms qs r) (parisiQSuffixDeriv ξ h ms qs r x) x) ∧
    (∃ C : ℝ,
      (∀ x, HasDerivAt (parisiQSuffixDeriv ξ h ms qs r)
        (parisiQSuffixDeriv2 ξ h ms qs r x) x) ∧
      Continuous (parisiQSuffixDeriv2 ξ h ms qs r) ∧
      (∀ x, |parisiQSuffixDeriv ξ h ms qs r x| ≤ 1) ∧
      ∀ x, |parisiQSuffixDeriv2 ξ h ms qs r x| ≤ C) := by
  apply coleHopfIterate_deriv_regular
  · exact hasDerivAt_parisiLogCoshTerminal h
  · exact hasDerivAt_parisiLogCoshTerminalDeriv h
  · exact continuous_parisiLogCoshTerminalDeriv2 h
  · exact fun x => (abs_parisiLogCoshTerminalDeriv_lt_one h x).le
  · exact abs_parisiLogCoshTerminalDeriv2_le_one h
  · intro p
    apply hm.mExt_pos
    simp

/-- At the first overlap coordinate, the inner derivative in the split moment is exactly the
spatial derivative of the full concrete Cole-Hopf recursion. -/
lemma parisiQFirstInner_eq_coleHopfIterateDeriv {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (x : ℝ) :
    (∫ w, parisiQSuffixDeriv ξ h ms qs 0 (x + w) *
        coleHopfQ (mExt ms 1)
          (Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ (qs 0)))
          (parisiQSuffix ξ h ms qs 0) x w
      ∂gaussianReal 0 (Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ (qs 0)))) =
      coleHopfIterateDeriv (k + 1) (parisiLevelMasses ms) (parisiLevelVars ξ qs)
        (parisiLogCoshTerminal h) (parisiLogCoshTerminalDeriv h) x := by
  have hms : Fin.tail (parisiLevelMasses ms) = parisiQSuffixMasses ms 0 := by
    funext p
    simp [Fin.tail, parisiQSuffixMasses, parisiLevelMasses_apply]
  have hvs : Fin.tail (parisiLevelVars ξ qs) = parisiQSuffixVars ξ qs 0 := by
    funext p
    simp [Fin.tail, parisiLevelVars, parisiQSuffixVars]
  rw [coleHopfIterateDeriv]
  rw [hms, hvs]
  simp only [parisiLevelMasses_apply, Fin.val_zero, zero_add]
  have hv : parisiLevelVars ξ qs 0 =
      Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ (qs 0)) := by
    simp [parisiLevelVars, parisiVar, qExt_succ_of_lt qs (Nat.succ_pos k)]
  rw [hv]
  rfl

/-- For a nonfirst coordinate, the concrete recursion splits into its unchanged prefix, the two
levels whose variances change, and the concrete suffix. -/
theorem parisiRecGauss_qUpdate_eq_split {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hr : 0 < r.val) (u z₀ : ℝ) :
    parisiRecGauss ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h) z₀ =
      coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
        (parisiQPrefixVars ξ qs r)
        (coleHopf (mExt ms r.val)
          (Real.toNNReal (deriv ξ u - deriv ξ (qExt qs r.val)))
          (coleHopf (mExt ms (r.val + 1))
            (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ u))
            (parisiQSuffix ξ h ms qs r))) z₀ := by
  rw [parisiRecGauss_eq_coleHopfIterate (qUpdate qs r u) hm]
  have hn : k + 1 = (r.val - 1) + (2 + (k - r.val)) := by omega
  rw [coleHopfIterate_split_two_of_eq (r.val - 1) (k - r.val) hn]
  congr 4
  · funext p
    unfold parisiLevelVars parisiQPrefixVars
    change parisiVar ξ (qUpdate qs r u) (p.val + 1) = parisiVar ξ qs (p.val + 1)
    rw [parisiVar_qUpdate_before]
    have hp := p.isLt
    omega
  · rw [parisiLevelMasses_apply]
    apply congrArg (mExt ms)
    change r.val - 1 + 1 = r.val
    omega
  · unfold parisiLevelVars
    have hre : r.val - 1 + 1 = r.val := by omega
    rw [hre, parisiVar_qUpdate_left]
  · apply Fin.ext
    simp
    omega
  · unfold parisiLevelVars
    have hre : r.val - 1 + 1 + 1 = r.val + 1 := by omega
    rw [hre, parisiVar_qUpdate_right]
  · funext p
    rw [parisiLevelMasses_apply]
    unfold parisiQSuffixMasses
    apply congrArg (mExt ms)
    change r.val - 1 + p.val + 2 + 1 = r.val + p.val + 2
    omega
  · funext p
    unfold parisiLevelVars parisiQSuffixVars
    rw [parisiVar_qUpdate_after]
    · apply congrArg (parisiVar ξ qs)
      change r.val - 1 + p.val + 2 + 1 = r.val + p.val + 2
      omega
    · change r.val + 1 < r.val - 1 + p.val + 2 + 1
      omega

/-- At the first coordinate, the changing inner level is followed by the same concrete suffix. -/
theorem parisiRecGauss_first_qUpdate_eq {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (u z₀ : ℝ) :
    parisiRecGauss ξ ms (qUpdate qs 0 u) (parisiLogCoshTerminal h) z₀ =
      coleHopf (mExt ms 1)
        (Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ u))
        (parisiQSuffix ξ h ms qs 0) z₀ := by
  rw [parisiRecGauss_eq_coleHopfIterate (qUpdate qs 0 u) hm,
    coleHopfIterate_succ]
  congr 3
  · funext p
    simp [Fin.tail, parisiQSuffixMasses]
  · funext p
    simp only [Fin.tail, parisiLevelVars, parisiQSuffixVars, Fin.val_succ, Fin.val_zero,
      Nat.sub_zero, Nat.zero_add]
    rw [parisiVar_qUpdate_after]
    simp

/-- The first overlap variation is exactly a two-level split with outer exponent zero. -/
theorem parisiX₀_first_qUpdate_eq_split {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (u : ℝ) :
    parisiX₀ ξ ms (qUpdate qs 0 u) (parisiLogCoshTerminal h) =
      coleHopf 0 (Real.toNNReal (deriv ξ u - deriv ξ (qExt qs 0)))
        (coleHopf (mExt ms 1)
          (Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ u))
          (parisiQSuffix ξ h ms qs 0)) 0 := by
  unfold parisiX₀
  rw [coleHopf_zero]
  have hv := parisiVar_qUpdate_left (ξ := ξ) qs (0 : Fin (k + 1)) u
  simp only [Fin.val_zero] at hv
  rw [hv]
  apply integral_congr_ae
  filter_upwards [] with z₀
  simpa using parisiRecGauss_first_qUpdate_eq qs hm u z₀

/-- If `ξ'` converges along an overlap variation, the corresponding concrete `X₀` values
converge uniformly in the external-field shift.  This includes the endpoint where one of the
two adjacent variances collapses to zero. -/
theorem tendsto_uniform_parisiX₀_qUpdate
    {α : Type*} {l : Filter α} {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ}
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : α → ℝ)
    (hm : ParisiMAdmissible ms)
    (hu : Filter.Tendsto (fun a => deriv ξ (u a)) l (nhds (deriv ξ (qs r)))) :
    ∀ ε > 0, ∀ᶠ a in l, ∀ h,
      |parisiX₀ ξ ms (qUpdate qs r (u a)) (parisiLogCoshTerminal h) -
        parisiX₀ ξ ms (qUpdate qs r (qs r)) (parisiLogCoshTerminal h)| < ε := by
  let A : ℝ → ℝ := parisiQSuffix ξ 0 ms qs r
  have hAreg := parisiQSuffix_deriv_regular (ξ := ξ) (h := 0) qs r hm
  have hAm : Measurable A := measurable_of_hasDerivAt hAreg.1
  have hAlip : ∀ x y, |A y - A x| ≤ 1 * |y - x| :=
    ProbabilityTheory.abs_sub_le_mul_abs_sub_of_hasDerivAt hAreg.1 hAreg.2.choose_spec.2.2.1
  let vL : α → ℝ≥0 := fun a =>
    Real.toNNReal (deriv ξ (u a) - deriv ξ (qExt qs r.val))
  let vR : α → ℝ≥0 := fun a =>
    Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (u a))
  let vL₀ : ℝ≥0 := Real.toNNReal
    (deriv ξ (qs r) - deriv ξ (qExt qs r.val))
  let vR₀ : ℝ≥0 := Real.toNNReal
    (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r))
  have hvL : Filter.Tendsto vL l (nhds vL₀) := by
    exact continuous_real_toNNReal.continuousAt.tendsto.comp
      (hu.sub_const (deriv ξ (qExt qs r.val)))
  have hvR : Filter.Tendsto vR l (nhds vR₀) := by
    exact continuous_real_toNNReal.continuousAt.tendsto.comp
      (hu.const_sub (deriv ξ (qExt qs (r.val + 2))))
  let T : α → ℝ → ℝ := fun a =>
    coleHopf (mExt ms r.val) (vL a)
      (coleHopf (mExt ms (r.val + 1)) (vR a) A)
  let T₀ : ℝ → ℝ :=
    coleHopf (mExt ms r.val) vL₀
      (coleHopf (mExt ms (r.val + 1)) vR₀ A)
  have hT := tendsto_uniform_coleHopf_two_of_tendsto_var hAm hAlip
    (mExt ms r.val) (mExt ms (r.val + 1)) hvL hvR
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  filter_upwards [hT (ε / 2) hhalf] with a ha
  intro h
  have htranslate (a : α) :
      coleHopf (mExt ms r.val) (vL a)
          (coleHopf (mExt ms (r.val + 1)) (vR a)
            (parisiQSuffix ξ h ms qs r)) = fun x => T a (h + x) := by
    have hAtrans : parisiQSuffix ξ h ms qs r = fun y => A (h + y) := by
      funext y
      exact parisiQSuffix_translate ξ h ms qs r y
    rw [hAtrans]
    have hinner :
        coleHopf (mExt ms (r.val + 1)) (vR a) (fun y => A (h + y)) =
          fun y => coleHopf (mExt ms (r.val + 1)) (vR a) A (h + y) := by
      funext y
      exact coleHopf_translate _ _ A h y
    rw [hinner]
    funext x
    exact coleHopf_translate _ _ _ h x
  have htranslate₀ :
      coleHopf (mExt ms r.val) vL₀
          (coleHopf (mExt ms (r.val + 1)) vR₀
            (parisiQSuffix ξ h ms qs r)) = fun x => T₀ (h + x) := by
    have hAtrans : parisiQSuffix ξ h ms qs r = fun y => A (h + y) := by
      funext y
      exact parisiQSuffix_translate ξ h ms qs r y
    rw [hAtrans]
    have hinner :
        coleHopf (mExt ms (r.val + 1)) vR₀ (fun y => A (h + y)) =
          fun y => coleHopf (mExt ms (r.val + 1)) vR₀ A (h + y) := by
      funext y
      exact coleHopf_translate _ _ A h y
    rw [hinner]
    funext x
    exact coleHopf_translate _ _ _ h x
  by_cases hr : r.val = 0
  · have hre : r = 0 := Fin.ext hr
    subst r
    rw [parisiX₀_first_qUpdate_eq_split qs hm (u a),
      parisiX₀_first_qUpdate_eq_split qs hm (qs 0)]
    have ht :
        coleHopf 0 (Real.toNNReal (deriv ξ (u a) - deriv ξ (qExt qs 0)))
            (coleHopf (mExt ms 1)
              (Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ (u a)))
              (parisiQSuffix ξ h ms qs 0)) 0 = T a h := by
      simpa [vL, vR, mExt_zero] using congrFun (htranslate a) 0
    have ht₀ :
        coleHopf 0 (Real.toNNReal (deriv ξ (qs 0) - deriv ξ (qExt qs 0)))
            (coleHopf (mExt ms 1)
              (Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ (qs 0)))
              (parisiQSuffix ξ h ms qs 0)) 0 = T₀ h := by
      simpa [vL₀, vR₀, mExt_zero] using congrFun htranslate₀ 0
    rw [ht, ht₀]
    exact (ha h).trans (half_lt_self hε)
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    have hTlip (a : α) : ∀ x y, |T a y - T a x| ≤ 1 * |y - x| := by
      dsimp [T]
      exact abs_coleHopf_sub_le_of_lipschitz _
        ((lipschitzWith_toNNReal_of_abs_sub_le
          (abs_coleHopf_sub_le_of_lipschitz _ hAm hAlip (vR a))).continuous.measurable)
        (abs_coleHopf_sub_le_of_lipschitz _ hAm hAlip (vR a)) (vL a)
    have hT₀lip : ∀ x y, |T₀ y - T₀ x| ≤ 1 * |y - x| := by
      dsimp [T₀]
      exact abs_coleHopf_sub_le_of_lipschitz _
        ((lipschitzWith_toNNReal_of_abs_sub_le
          (abs_coleHopf_sub_le_of_lipschitz _ hAm hAlip vR₀)).continuous.measurable)
        (abs_coleHopf_sub_le_of_lipschitz _ hAm hAlip vR₀) vL₀
    have hTm : Measurable (T a) :=
      (lipschitzWith_toNNReal_of_abs_sub_le (hTlip a)).continuous.measurable
    have hT₀m : Measurable T₀ :=
      (lipschitzWith_toNNReal_of_abs_sub_le hT₀lip).continuous.measurable
    have hpref : ∀ x,
        |coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
            (parisiQPrefixVars ξ qs r) (T a) x -
          coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
            (parisiQPrefixVars ξ qs r) T₀ x| ≤ ε / 2 :=
      abs_coleHopfIterate_sub_le_of_sup _ _ hTm (hTlip a) hT₀m hT₀lip
        (fun x => (ha x).le)
    unfold parisiX₀
    rw [parisiVar_qUpdate_before qs r (u a) hrpos,
      parisiVar_qUpdate_before qs r (qs r) hrpos]
    have hrec (a : α) (z₀ : ℝ) :
        parisiRecGauss ξ ms (qUpdate qs r (u a)) (parisiLogCoshTerminal h) z₀ =
          coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
            (parisiQPrefixVars ξ qs r) (T a) (h + z₀) := by
      rw [parisiRecGauss_qUpdate_eq_split qs r hm hrpos (u a) z₀,
        htranslate a, coleHopfIterate_translate]
    have hrec₀ (z₀ : ℝ) :
        parisiRecGauss ξ ms (qUpdate qs r (qs r)) (parisiLogCoshTerminal h) z₀ =
          coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
            (parisiQPrefixVars ξ qs r) T₀ (h + z₀) := by
      rw [parisiRecGauss_qUpdate_eq_split qs r hm hrpos (qs r) z₀,
        htranslate₀, coleHopfIterate_translate]
    have hUaLip := abs_coleHopfIterate_sub_le (r.val - 1)
      (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r) hTm (hTlip a)
    have hU₀Lip := abs_coleHopfIterate_sub_le (r.val - 1)
      (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r) hT₀m hT₀lip
    have hUaM :=
      (lipschitzWith_toNNReal_of_abs_sub_le hUaLip).continuous.measurable
    have hU₀M :=
      (lipschitzWith_toNNReal_of_abs_sub_le hU₀Lip).continuous.measurable
    have hUaI : Integrable (fun z₀ =>
        coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
          (parisiQPrefixVars ξ qs r) (T a) (h + z₀))
        (gaussianReal 0 (parisiVar ξ qs 0)) :=
      ((HasLinearGrowth.of_lipschitz hUaLip).comp_add_const h).toHasExpGrowth
        |>.integrable_gaussianReal
          (hUaM.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    have hU₀I : Integrable (fun z₀ =>
        coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
          (parisiQPrefixVars ξ qs r) T₀ (h + z₀))
        (gaussianReal 0 (parisiVar ξ qs 0)) :=
      ((HasLinearGrowth.of_lipschitz hU₀Lip).comp_add_const h).toHasExpGrowth
        |>.integrable_gaussianReal
          (hU₀M.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    simp_rw [hrec, hrec₀]
    rw [← integral_sub hUaI hU₀I]
    have hbound : ‖∫ z₀,
        coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
            (parisiQPrefixVars ξ qs r) (T a) (h + z₀) -
          coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
            (parisiQPrefixVars ξ qs r) T₀ (h + z₀)
        ∂gaussianReal 0 (parisiVar ξ qs 0)‖ ≤ ε / 2 :=
      by
        have hb := norm_integral_le_of_norm_le_const
          (μ := gaussianReal 0 (parisiVar ξ qs 0))
          (f := fun z₀ =>
            coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
                (parisiQPrefixVars ξ qs r) (T a) (h + z₀) -
              coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
                (parisiQPrefixVars ξ qs r) T₀ (h + z₀))
          (C := ε / 2) (Filter.Eventually.of_forall fun z₀ => by
            simpa only [Real.norm_eq_abs] using hpref (h + z₀))
        simpa using hb
    rw [Real.norm_eq_abs] at hbound
    exact hbound.trans_lt (half_lt_self hε)

/-- Talagrand's concrete moment
`E(W₁ ⋯ W_{r-1} A'_r(ζ_r)^2)` for the overlap coordinate represented by `r`. -/
noncomputable def parisiQMoment (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) : ℝ :=
  if r.val = 0 then
    coleHopfSplitMoment (mExt ms (r.val + 1)) (mExt ms r.val)
      (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)))
      (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)))
      (parisiQSuffix ξ h ms qs r) (parisiQSuffixDeriv ξ h ms qs r) 0
  else
    ∫ z₀, ∫ zs, coleHopfSplitMoment (mExt ms (r.val + 1)) (mExt ms r.val)
        (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)))
        (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)))
        (parisiQSuffix ξ h ms qs r) (parisiQSuffixDeriv ξ h ms qs r)
        (z₀ + ∑ p, zs p)
      ∂cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
        (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
        (fun zs => ENNReal.ofReal (Real.exp
          (coleHopf (mExt ms r.val)
            (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)))
            (coleHopf (mExt ms (r.val + 1))
              (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)))
              (parisiQSuffix ξ h ms qs r)) (z₀ + ∑ p, zs p))))
      ∂gaussianReal 0 (parisiVar ξ qs 0)

/-- The actual `parisiX₀` derivative, with the abstract moment replaced by the concrete recursive
expectation in `parisiQMoment`. This is (14.219) propagated through all earlier levels. -/
theorem hasDerivAt_parisiX₀_qUpdate
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} {ms : Fin k → ℝ}
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (hm : ParisiMAdmissible ms) {ξ₂ : ℝ}
    (hξ' : HasDerivAt (deriv ξ) ξ₂ (qs r))
    (hleft : deriv ξ (qExt qs r.val) < deriv ξ (qs r))
    (hright : deriv ξ (qs r) < deriv ξ (qExt qs (r.val + 2))) :
    HasDerivAt
      (fun u => parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h))
      ((-1 / 2 : ℝ) * ξ₂ * (mExt ms (r.val + 1) - mExt ms r.val) *
        parisiQMoment ξ h ms qs r) (qs r) := by
  obtain ⟨hA, C, hA', hA''c, hA'b, hA''b⟩ :=
    parisiQSuffix_deriv_regular (ξ := ξ) (h := h) qs r hm
  by_cases hr : r.val = 0
  · have hrfin : r = 0 := Fin.ext hr
    subst r
    have hd := hasDerivAt_coleHopf_coleHopf_q
      (ξ := ξ) (ξ₂ := ξ₂) (qL := qExt qs 0) (q := qs 0) (qR := qExt qs 2)
      (m := mExt ms 1) (m' := 0) (A := parisiQSuffix ξ h ms qs 0)
      (A' := parisiQSuffixDeriv ξ h ms qs 0)
      (A'' := parisiQSuffixDeriv2 ξ h ms qs 0) hA hA' hA''c hA'b hA''b
      (ne_of_gt (hm.mExt_pos (by omega : 0 < 1))) hξ' hleft hright 0
    have hfun :
        (fun u => parisiX₀ ξ ms (qUpdate qs 0 u) (parisiLogCoshTerminal h)) =
          (fun u => coleHopf 0 (Real.toNNReal (deriv ξ u - deriv ξ (qExt qs 0)))
            (coleHopf (mExt ms 1)
              (Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ u))
              (parisiQSuffix ξ h ms qs 0)) 0) := by
      funext u
      exact parisiX₀_first_qUpdate_eq_split qs hm u
    rw [hfun]
    convert hd using 1 <;> simp [parisiQMoment, mExt_zero]
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    have hfun :
        (fun u => parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h)) =
          (fun u => ∫ z₀, coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
            (parisiQPrefixVars ξ qs r)
            (fun y => coleHopf (mExt ms r.val)
              (Real.toNNReal (deriv ξ u - deriv ξ (qExt qs r.val)))
              (coleHopf (mExt ms (r.val + 1))
                (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ u))
                (parisiQSuffix ξ h ms qs r)) y) z₀
            ∂gaussianReal 0 (parisiVar ξ qs 0)) := by
      funext u
      unfold parisiX₀
      rw [parisiVar_qUpdate_before qs r u (by omega : 0 < r.val)]
      apply integral_congr_ae
      filter_upwards [] with z₀
      exact parisiRecGauss_qUpdate_eq_split qs r hm hrpos u z₀
    rw [hfun]
    have hd := hasDerivAt_integral_coleHopfIterate_q
      (ξ := ξ) (ξ₂ := ξ₂) (qL := qExt qs r.val) (q := qs r)
      (qR := qExt qs (r.val + 2)) (m := mExt ms (r.val + 1))
      (m' := mExt ms r.val) (A := parisiQSuffix ξ h ms qs r)
      (A' := parisiQSuffixDeriv ξ h ms qs r)
      (A'' := parisiQSuffixDeriv2 ξ h ms qs r)
      (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
      hA hA' hA''c hA'b hA''b
      (fun p => hm.mExt_pos (by simp [parisiQPrefixMasses]))
      (fun p => mExt_le_one (fun i => (hm.2.2 i).le) _)
      (ne_of_gt (hm.mExt_pos (by omega : 0 < r.val + 1))) hξ' hleft hright
      (parisiVar ξ qs 0) 0
    convert hd using 1
    simp only [zero_add]
    unfold parisiQMoment
    rw [if_neg hr]
    unfold coleHopfSplitMoment
    simp only [integral_const_mul]
    ring

/-- The concrete recursive moment always lies in the closed unit interval in absolute value. -/
theorem abs_parisiQMoment_le_one {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hm : ParisiMAdmissible ms) : |parisiQMoment ξ h ms qs r| ≤ 1 := by
  obtain ⟨hA, C, hA', hA''c, hA'b, hA''b⟩ :=
    parisiQSuffix_deriv_regular (ξ := ξ) (h := h) qs r hm
  by_cases hr : r.val = 0
  · unfold parisiQMoment
    rw [if_pos hr]
    exact abs_coleHopfSplitMoment_le_one hA hA' hA'b 0
  · let A : ℝ → ℝ := parisiQSuffix ξ h ms qs r
    let B : ℝ → ℝ := coleHopf (mExt ms (r.val + 1))
      (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r))) A
    let G : ℝ → ℝ := coleHopf (mExt ms r.val)
      (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val))) B
    have hAm : Measurable A := measurable_of_hasDerivAt hA
    have hAlip : ∀ x y, |A y - A x| ≤ 1 * |y - x| :=
      ProbabilityTheory.abs_sub_le_mul_abs_sub_of_hasDerivAt hA hA'b
    have hBlip : ∀ x y, |B y - B x| ≤ 1 * |y - x| :=
      abs_coleHopf_sub_le_of_lipschitz _ hAm hAlip _
    have hBm : Measurable B :=
      (lipschitzWith_toNNReal_of_abs_sub_le hBlip).continuous.measurable
    have hGlip : ∀ x y, |G y - G x| ≤ 1 * |y - x| :=
      abs_coleHopf_sub_le_of_lipschitz _ hBm hBlip _
    have hGm : Measurable G :=
      (lipschitzWith_toNNReal_of_abs_sub_le hGlip).continuous.measurable
    have hprefix_pos : ∀ p, 0 < parisiQPrefixMasses ms r p := fun p =>
      hm.mExt_pos (by simp [parisiQPrefixMasses])
    have hprefix_le : ∀ p, parisiQPrefixMasses ms r p ≤ 1 := fun p =>
      mExt_le_one (fun i => (hm.2.2 i).le) _
    have hcascade : ∀ z₀ : ℝ,
        |∫ zs, coleHopfSplitMoment (mExt ms (r.val + 1)) (mExt ms r.val)
            (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)))
            (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)))
            A (parisiQSuffixDeriv ξ h ms qs r) (z₀ + ∑ p, zs p)
          ∂cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
            (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
            (fun zs => ENNReal.ofReal (Real.exp (G (z₀ + ∑ p, zs p))))| ≤ 1 := by
      intro z₀
      apply abs_integral_cascadeTiltMeasure_le
        (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
        hprefix_pos hprefix_le hGm hGlip z₀
      intro y
      exact abs_coleHopfSplitMoment_le_one hA hA' hA'b y
    unfold parisiQMoment
    rw [if_neg hr]
    change |∫ z₀, ∫ zs, coleHopfSplitMoment (mExt ms (r.val + 1)) (mExt ms r.val)
        (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)))
        (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)))
        A (parisiQSuffixDeriv ξ h ms qs r) (z₀ + ∑ p, zs p)
      ∂cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
        (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
        (fun zs => ENNReal.ofReal (Real.exp (G (z₀ + ∑ p, zs p))))
      ∂gaussianReal 0 (parisiVar ξ qs 0)| ≤ 1
    have hb := norm_integral_le_of_norm_le_const
      (μ := gaussianReal 0 (parisiVar ξ qs 0))
      (f := fun z₀ => ∫ zs, coleHopfSplitMoment (mExt ms (r.val + 1))
        (mExt ms r.val)
        (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)))
        (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)))
        A (parisiQSuffixDeriv ξ h ms qs r) (z₀ + ∑ p, zs p)
        ∂cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
          (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
          (fun zs => ENNReal.ofReal (Real.exp (G (z₀ + ∑ p, zs p)))))
      (C := 1) (Filter.Eventually.of_forall fun z₀ => by
        rw [Real.norm_eq_abs]
        exact hcascade z₀)
    simpa [probReal_univ, Real.norm_eq_abs] using hb

theorem parisiQMoment_nonneg (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) :
    0 ≤ parisiQMoment ξ h ms qs r := by
  unfold parisiQMoment
  split_ifs
  · exact coleHopfSplitMoment_nonneg _ _ _ _ _ _ _
  · apply integral_nonneg
    intro z₀
    apply integral_nonneg
    intro zs
    exact coleHopfSplitMoment_nonneg _ _ _ _ _ _ _

theorem parisiQMoment_first_eq_sq_full_deriv {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hqzero : qs 0 = 0) :
    parisiQMoment ξ h ms qs 0 =
      coleHopfIterateDeriv (k + 1) (parisiLevelMasses ms) (parisiLevelVars ξ qs)
        (parisiLogCoshTerminal h) (parisiLogCoshTerminalDeriv h) 0 ^ 2 := by
  have hvL : Real.toNNReal (deriv ξ (qs 0) - deriv ξ (qExt qs 0)) = 0 := by
    rw [hqzero, qExt_zero]
    simp
  have hinner := parisiQFirstInner_eq_coleHopfIterateDeriv
    (ξ := ξ) (h := h) ms qs 0
  unfold parisiQMoment
  simp only [Fin.val_zero, zero_add]
  unfold coleHopfSplitMoment
  rw [hvL]
  simp only [gaussianReal_zero_var, integral_dirac, add_zero]
  rw [hinner]
  simp only [if_true, mExt_zero, coleHopfQ, zero_mul, Real.exp_zero, mul_one]

/-- The first concrete moment varies continuously from the admissible endpoint `q₁ = 0`.
This is the nearby-sign input needed when `ξ''(0)` itself vanishes. -/
theorem continuousAt_parisiQMoment_first_qUpdate_zero
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} {ms : Fin k → ℝ}
    (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) :
    ContinuousAt (fun u => parisiQMoment ξ h ms (qUpdate qs 0 u) 0) 0 := by
  obtain ⟨hA, C, hA', hA''c, hA'b, hA''b⟩ :=
    parisiQSuffix_deriv_regular (ξ := ξ) (h := h) qs 0 hm
  let S : (ℝ × ℝ) × ℝ → ℝ := fun p =>
    coleHopfSplitMoment (mExt ms 1) 0 (Real.toNNReal p.1.1)
      (Real.toNNReal p.1.2) (parisiQSuffix ξ h ms qs 0)
      (parisiQSuffixDeriv ξ h ms qs 0) p.2
  have hSc : Continuous S :=
    continuous_coleHopfSplitMoment_zero_outer_var hA hA' hA'b
  let P : ℝ → (ℝ × ℝ) × ℝ := fun u =>
    ((deriv ξ (qExt qs 2) - deriv ξ u,
      deriv ξ u - deriv ξ (qExt qs 0)), 0)
  have hPc : ContinuousAt P 0 := by
    have hd0 : ContinuousAt (deriv ξ) 0 :=
      (hξ.hasDeriv_deriv 0 ⟨le_rfl, zero_le_one⟩).continuousAt
    exact ((continuousAt_const.sub hd0).prodMk
      (hd0.sub continuousAt_const)).prodMk continuousAt_const
  have hc : ContinuousAt (fun u => S (P u)) 0 :=
    ContinuousAt.comp hSc.continuousAt hPc
  apply hc.congr_of_eventuallyEq
  filter_upwards [] with u
  have hext : qExt (qUpdate qs 0 u) 2 = qExt qs 2 :=
    qExt_qUpdate_of_gt qs 0 u (n := 2) (by norm_num)
  unfold parisiQMoment S P
  simp only [Fin.val_zero, if_true, qUpdate_self, qExt_zero]
  rw [hext, parisiQSuffix_qUpdate, parisiQSuffixDeriv_qUpdate]
  simp [mExt_zero]

/-- When the first overlap is zero, every nonzero external field gives a strictly positive
first concrete moment. -/
theorem parisiQMoment_first_pos_of_ne_zero {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hqzero : qs 0 = 0) (hh : h ≠ 0) :
    0 < parisiQMoment ξ h ms qs 0 := by
  have hlevelpos : ∀ i, 0 < parisiLevelMasses ms i := by
    intro i
    rw [parisiLevelMasses_apply]
    exact hm.mExt_pos (by omega)
  let d : ℝ := coleHopfIterateDeriv (k + 1) (parisiLevelMasses ms)
    (parisiLevelVars ξ qs) (parisiLogCoshTerminal h)
    (parisiLogCoshTerminalDeriv h) 0
  have hd : d ≠ 0 :=
    coleHopfIterateDeriv_parisiLogCoshTerminal_ne_zero
      (parisiLevelMasses ms) (parisiLevelVars ξ qs) hlevelpos hh
  rw [parisiQMoment_first_eq_sq_full_deriv ms qs hqzero]
  exact sq_pos_of_ne_zero hd

/-- At the upper endpoint, the concrete final moment is strictly below one.  The strictness
comes from `$|\tanh x|<1$` and is preserved by the preceding Cole-Hopf cascade and the root
Gaussian average. -/
theorem parisiQMoment_last_lt_one {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hqlast : qs (Fin.last k) = 1) :
    parisiQMoment ξ h ms qs (Fin.last k) < 1 := by
  let r : Fin (k + 1) := Fin.last k
  obtain ⟨hA, C, hA', hA''c, hA'b, hA''b⟩ :=
    parisiQSuffix_deriv_regular (ξ := ξ) (h := h) qs r hm
  have hrval : r.val = k := by simp [r]
  have hAeq : parisiQSuffix ξ h ms qs r = parisiLogCoshTerminal h := by
    unfold parisiQSuffix
    exact coleHopfIterate_eq_terminal_of_eq_zero (by omega) _ _ _
  have hA'eq : parisiQSuffixDeriv ξ h ms qs r = parisiLogCoshTerminalDeriv h := by
    unfold parisiQSuffixDeriv
    exact coleHopfIterateDeriv_eq_terminal_of_eq_zero (by omega) _ _ _ _
  have hqright : qExt qs (r.val + 2) = 1 := qExt_of_le qs (by simp [hrval])
  have hvR : Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)) = 0 := by
    rw [hqright]
    have hr : r = Fin.last k := rfl
    rw [hr, hqlast]
    simp
  let f : ℝ → ℝ := fun x =>
    coleHopfSplitMoment (mExt ms (r.val + 1)) (mExt ms r.val)
      (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)))
      (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)))
      (parisiQSuffix ξ h ms qs r) (parisiQSuffixDeriv ξ h ms qs r) x
  have hfc : Continuous f :=
    continuous_coleHopfSplitMoment hA hA' hA'b
  have hfb : ∀ x, |f x| ≤ 1 := fun x =>
    abs_coleHopfSplitMoment_le_one hA hA' hA'b x
  have hflt : ∀ x, f x < 1 := by
    intro x
    dsimp [f]
    rw [hvR]
    apply coleHopfSplitMoment_lt_one_of_zero_right hA hA'
    intro y
    rw [hA'eq]
    exact abs_parisiLogCoshTerminalDeriv_lt_one h y
  by_cases hk : k = 0
  · subst k
    unfold parisiQMoment
    rw [if_pos (by simp)]
    exact hflt 0
  · have hrpos : 0 < r.val := by omega
    let A : ℝ → ℝ := parisiQSuffix ξ h ms qs r
    let B : ℝ → ℝ := coleHopf (mExt ms (r.val + 1))
      (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r))) A
    let G : ℝ → ℝ := coleHopf (mExt ms r.val)
      (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val))) B
    have hAm : Measurable A := measurable_of_hasDerivAt hA
    have hAlip : ∀ x y, |A y - A x| ≤ 1 * |y - x| :=
      ProbabilityTheory.abs_sub_le_mul_abs_sub_of_hasDerivAt hA hA'b
    have hBlip : ∀ x y, |B y - B x| ≤ 1 * |y - x| :=
      abs_coleHopf_sub_le_of_lipschitz _ hAm hAlip _
    have hBm : Measurable B :=
      (lipschitzWith_toNNReal_of_abs_sub_le hBlip).continuous.measurable
    have hGlip : ∀ x y, |G y - G x| ≤ 1 * |y - x| :=
      abs_coleHopf_sub_le_of_lipschitz _ hBm hBlip _
    have hGm : Measurable G :=
      (lipschitzWith_toNNReal_of_abs_sub_le hGlip).continuous.measurable
    have hprefix_pos : ∀ p, 0 < parisiQPrefixMasses ms r p := fun p =>
      hm.mExt_pos (by simp [parisiQPrefixMasses])
    have hprefix_le : ∀ p, parisiQPrefixMasses ms r p ≤ 1 := fun p =>
      mExt_le_one (fun i => (hm.2.2 i).le) _
    let F : ℝ → ℝ := fun z₀ =>
      ∫ zs, f (z₀ + ∑ p, zs p)
        ∂cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
          (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
          (fun zs => ENNReal.ofReal (Real.exp (G (z₀ + ∑ p, zs p))))
    have hFm : Measurable F :=
      measurable_integral_cascadeTiltMeasure_comp_add_sum
        (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
        hprefix_pos hprefix_le hGm hGlip hfc.measurable
    have hFb : ∀ z₀, |F z₀| ≤ 1 := by
      intro z₀
      exact abs_integral_cascadeTiltMeasure_le
        (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
        hprefix_pos hprefix_le hGm hGlip z₀ hfb
    have hFlt : ∀ z₀, F z₀ < 1 := by
      intro z₀
      let μ := cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
        (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
        (fun zs => ENNReal.ofReal (Real.exp (G (z₀ + ∑ p, zs p))))
      letI : IsProbabilityMeasure μ :=
        isProbabilityMeasure_cascadeTiltMeasure_comp_add_sum
          (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
          hprefix_pos hprefix_le hGm hGlip z₀
      apply integral_lt_one_of_measurable_of_lt
      · exact hfc.measurable.comp (measurable_const.add
          (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))
      · exact fun zs => hfb _
      · exact fun zs => hflt _
    have hroot : ∫ z₀, F z₀ ∂gaussianReal 0 (parisiVar ξ qs 0) < 1 :=
      integral_lt_one_of_measurable_of_lt hFm hFb hFlt
    unfold parisiQMoment
    rw [if_neg (by simpa [r] using ne_of_gt hrpos)]
    change (∫ z₀, F z₀ ∂gaussianReal 0 (parisiVar ξ qs 0)) < 1
    exact hroot

/-- After absorbing the exponent-one terminal layer, differentiation of its remaining variance
produces the final concrete moment, including the case with no mass parameters. -/
theorem hasDerivAt_parisiLastAbsorbed
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} {ms : Fin k → ℝ}
    (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs)
    (hqlast : qs (Fin.last k) = 1) :
    let r : Fin (k + 1) := Fin.last k
    let a : ℝ := deriv ξ 1 - deriv ξ (qExt qs r.val)
    let w₀ : ℝ≥0 := if r.val = 0 then 0 else parisiVar ξ qs 0
    HasDerivAt
      (fun s => ∫ z₀, coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
        (parisiQPrefixVars ξ qs r)
        (fun y => coleHopf (mExt ms r.val) (Real.toNNReal s)
          (parisiLogCoshTerminal h) y + (a - s) / 2) z₀ ∂gaussianReal 0 w₀)
      ((-(1 - mExt ms r.val) / 2) * parisiQMoment ξ h ms qs r) a := by
  dsimp only
  let r : Fin (k + 1) := Fin.last k
  let a : ℝ := deriv ξ 1 - deriv ξ (qExt qs r.val)
  let w₀ : ℝ≥0 := if r.val = 0 then 0 else parisiVar ξ qs 0
  have hrval : r.val = k := by simp [r]
  have hqLlt : qExt qs r.val < 1 := by
    by_cases hk : k = 0
    · subst k
      simp [r, qExt_zero]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      change qExt qs k < 1
      have hprev : (⟨k - 1, by omega⟩ : Fin (k + 1)) < Fin.last k := by
        exact Fin.mk_lt_mk.mpr (by simp [Fin.last]; omega)
      rw [qExt, if_neg hk, dif_pos (by omega : k - 1 < k + 1)]
      simpa [hqlast] using hq.1 hprev
  have hqLmem : qExt qs r.val ∈ Icc (0 : ℝ) 1 :=
    qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _
  have ha : 0 < a := by
    dsimp [a]
    exact sub_pos.mpr (hξ.strictMonoOn_deriv hqLmem ⟨zero_le_one, le_rfl⟩ hqLlt)
  have hmnonneg : 0 ≤ mExt ms r.val := by
    by_cases hr0 : r.val = 0
    · rw [hr0, mExt_zero]
    · exact (hm.mExt_pos (Nat.pos_of_ne_zero hr0)).le
  have hmle : mExt ms r.val ≤ 1 := mExt_le_one (fun i => (hm.2.2 i).le) _
  have hd := hasDerivAt_integral_coleHopfIterate_absorbed_last
    (a := a) (s₀ := a)
    (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
    (fun p => hm.mExt_pos (by simp [parisiQPrefixMasses]))
    (fun p => mExt_le_one (fun i => (hm.2.2 i).le) _)
    hmnonneg hmle ha
    (hasDerivAt_parisiLogCoshTerminal h)
    (hasDerivAt_parisiLogCoshTerminalDeriv h)
    (continuous_parisiLogCoshTerminalDeriv2 h)
    (fun y => (abs_parisiLogCoshTerminalDeriv_lt_one h y).le)
    (abs_parisiLogCoshTerminalDeriv2_le_one h) w₀
  convert hd using 1
  have hAg : HasLinearGrowth (parisiLogCoshTerminal h) :=
    HasLinearGrowth.of_bounded_deriv (hasDerivAt_parisiLogCoshTerminal h)
      (fun y => (abs_parisiLogCoshTerminalDeriv_lt_one h y).le)
  have hAm : Measurable (parisiLogCoshTerminal h) :=
    measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal h)
  have hA'm : Measurable (parisiLogCoshTerminalDeriv h) :=
    measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminalDeriv h)
  have hinner (y : ℝ) :
      (1 / 2 : ℝ) * ∫ z,
          (parisiLogCoshTerminalDeriv2 h (y + z) +
            mExt ms r.val * parisiLogCoshTerminalDeriv h (y + z) ^ 2) *
            coleHopfQ (mExt ms r.val) (Real.toNNReal a)
              (parisiLogCoshTerminal h) y z ∂gaussianReal 0 (Real.toNNReal a) - 1 / 2 =
        (-(1 - mExt ms r.val) / 2) *
          ∫ z, parisiLogCoshTerminalDeriv h (y + z) ^ 2 *
            coleHopfQ (mExt ms r.val) (Real.toNNReal a)
              (parisiLogCoshTerminal h) y z ∂gaussianReal 0 (Real.toNNReal a) := by
    let Q : ℝ → ℝ := fun z => coleHopfQ (mExt ms r.val) (Real.toNNReal a)
      (parisiLogCoshTerminal h) y z
    have hQi : Integrable Q (gaussianReal 0 (Real.toNNReal a)) := by
      by_cases hm0 : mExt ms r.val = 0
      · simpa [Q, hm0, coleHopfQ_zero] using
          (integrable_const (μ := gaussianReal 0 (Real.toNNReal a)) (1 : ℝ))
      · exact integrable_coleHopfQ hAg hAm hm0 _ _
    have hQone : ∫ z, Q z ∂gaussianReal 0 (Real.toNNReal a) = 1 := by
      by_cases hm0 : mExt ms r.val = 0
      · simp [Q, hm0, coleHopfQ_zero]
      · exact integral_coleHopfQ hAg hAm hm0 _ _
    have hsqg : HasExpGrowth fun x => parisiLogCoshTerminalDeriv h x ^ 2 :=
      HasExpGrowth.of_bounded (C := 1) fun x => by
        rw [abs_pow]
        nlinarith [abs_nonneg (parisiLogCoshTerminalDeriv h x),
          (abs_parisiLogCoshTerminalDeriv_lt_one h x).le]
    have hsqI : Integrable (fun z => parisiLogCoshTerminalDeriv h (y + z) ^ 2 * Q z)
        (gaussianReal 0 (Real.toNNReal a)) := by
      by_cases hm0 : mExt ms r.val = 0
      · simp only [Q, hm0, coleHopfQ_zero, mul_one]
        exact (hsqg.comp_add_const y).integrable_gaussianReal
          ((hA'm.pow_const 2).comp (measurable_const.add measurable_id)).aestronglyMeasurable
      · exact integrable_mul_coleHopfQ hAg hAm hm0 hsqg
          (hA'm.pow_const 2) _ _
    have hexpand :
        (∫ z, (parisiLogCoshTerminalDeriv2 h (y + z) +
              mExt ms r.val * parisiLogCoshTerminalDeriv h (y + z) ^ 2) * Q z
            ∂gaussianReal 0 (Real.toNNReal a)) =
          1 + (mExt ms r.val - 1) *
            ∫ z, parisiLogCoshTerminalDeriv h (y + z) ^ 2 * Q z
              ∂gaussianReal 0 (Real.toNNReal a) := by
      have hpoint : ∀ z,
          (parisiLogCoshTerminalDeriv2 h (y + z) +
              mExt ms r.val * parisiLogCoshTerminalDeriv h (y + z) ^ 2) * Q z =
            Q z + (mExt ms r.val - 1) *
              (parisiLogCoshTerminalDeriv h (y + z) ^ 2 * Q z) := by
        intro z
        simp only [parisiLogCoshTerminalDeriv2, parisiLogCoshTerminalDeriv]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
        integral_add hQi (hsqI.const_mul (mExt ms r.val - 1)),
        integral_const_mul, hQone]
    change (1 / 2 : ℝ) * ∫ z,
        (parisiLogCoshTerminalDeriv2 h (y + z) +
          mExt ms r.val * parisiLogCoshTerminalDeriv h (y + z) ^ 2) * Q z
          ∂gaussianReal 0 (Real.toNNReal a) - 1 / 2 = _
    rw [hexpand]
    ring
  simp_rw [hinner]
  simp_rw [integral_const_mul]
  congr 1
  by_cases hk : k = 0
  · subst k
    let B : ℝ → ℝ := coleHopf 0 (Real.toNNReal a) (parisiLogCoshTerminal h)
    have hBlip : ∀ x y, |B y - B x| ≤ 1 * |y - x| :=
      abs_coleHopf_sub_le_of_lipschitz 0 hAm
        (ProbabilityTheory.abs_sub_le_mul_abs_sub_of_hasDerivAt
          (hasDerivAt_parisiLogCoshTerminal h)
          (fun y => (abs_parisiLogCoshTerminalDeriv_lt_one h y).le)) _
    have hBm : Measurable B :=
      (lipschitzWith_toNNReal_of_abs_sub_le hBlip).continuous.measurable
    let μ := cascadeTiltMeasure 0 (parisiQPrefixMasses ms 0)
      (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs 0 p))
      (fun zs => ENNReal.ofReal (Real.exp (B (0 + ∑ p, zs p))))
    letI : IsProbabilityMeasure μ :=
      isProbabilityMeasure_cascadeTiltMeasure_comp_add_sum
        (parisiQPrefixMasses ms 0) (parisiQPrefixVars ξ qs 0)
        (fun p => Fin.elim0 p) (fun p => Fin.elim0 p) hBm hBlip 0
    simp [r, w₀, a, parisiQMoment, coleHopfSplitMoment, parisiQSuffix,
      parisiQSuffixDeriv, hqlast, coleHopfQ_zero, B, μ, probReal_univ]
    change _ = μ.real Set.univ * _
    rw [probReal_univ, one_mul]
    have hq0 : qs 0 = 1 := by simpa using hqlast
    have hqright : qExt qs 2 = 1 := qExt_of_le qs (by omega)
    have hmright : mExt ms 1 = 1 := mExt_eq_one_of_le ms (by omega)
    simp [hq0, hqright, hmright, coleHopfQ, coleHopfIterateDeriv]
  · have hrpos : 0 < r.val := by simp [r, Nat.pos_of_ne_zero hk]
    have hAeq : parisiQSuffix ξ h ms qs r = parisiLogCoshTerminal h := by
      unfold parisiQSuffix
      exact coleHopfIterate_eq_terminal_of_eq_zero (by omega) _ _ _
    have hA'eq : parisiQSuffixDeriv ξ h ms qs r =
        parisiLogCoshTerminalDeriv h := by
      unfold parisiQSuffixDeriv
      exact coleHopfIterateDeriv_eq_terminal_of_eq_zero (by omega) _ _ _ _
    have hqright : qExt qs (r.val + 2) = 1 := qExt_of_le qs (by simp [hrval])
    have hvR : Real.toNNReal
        (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)) = 0 := by
      rw [hqright, show qs r = 1 by simpa [r] using hqlast]
      simp
    have hvL : Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)) =
        Real.toNNReal a := by
      rw [show qs r = 1 by simpa [r] using hqlast]
    have hmright : mExt ms (r.val + 1) = 1 := by
      rw [hrval]
      exact mExt_eq_one_of_le ms (by omega)
    have hw₀ : w₀ = parisiVar ξ qs 0 := by simp [w₀, ne_of_gt hrpos]
    unfold parisiQMoment
    rw [if_neg (ne_of_gt hrpos), hAeq, hA'eq, hvR, hvL, hmright, hw₀]
    simp only [coleHopfSplitMoment, gaussianReal_zero_var, integral_dirac, add_zero,
      mul_one]
    have hCH : coleHopf 1 0 (parisiLogCoshTerminal h) = parisiLogCoshTerminal h := by
      funext x
      exact coleHopf_zero_var 1 (parisiLogCoshTerminal h) x
    have hQ0 : ∀ y, coleHopfQ 1 0 (parisiLogCoshTerminal h) y 0 = 1 := by
      intro y
      simp [coleHopfQ, hCH]
    simp_rw [hCH, hQ0]
    simp [r]

/-- The theta-sum form of the Parisi functional, indexed by `Fin (k + 1)` rather than naturals. -/
theorem hasDerivWithinAt_parisiX₀_last_qUpdate
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} {ms : Fin k → ℝ}
    (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs)
    (hqlast : qs (Fin.last k) = 1) :
    HasDerivWithinAt
      (fun u => parisiX₀ ξ ms (qUpdate qs (Fin.last k) u) (parisiLogCoshTerminal h))
      ((-1 / 2 : ℝ) * deriv (deriv ξ) 1 *
        (1 - mExt ms k) * parisiQMoment ξ h ms qs (Fin.last k)) (Iic 1) 1 := by
  let r : Fin (k + 1) := Fin.last k
  let a : ℝ := deriv ξ 1 - deriv ξ (qExt qs r.val)
  let w₀ : ℝ≥0 := if r.val = 0 then 0 else parisiVar ξ qs 0
  let S : ℝ → ℝ := fun u => deriv ξ u - deriv ξ (qExt qs r.val)
  let J : ℝ → ℝ := fun s => ∫ z₀,
    coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
      (fun y => coleHopf (mExt ms r.val) (Real.toNNReal s)
        (parisiLogCoshTerminal h) y + (a - s) / 2) z₀ ∂gaussianReal 0 w₀
  have hJ : HasDerivAt J
      ((-(1 - mExt ms r.val) / 2) * parisiQMoment ξ h ms qs r) a :=
    hasDerivAt_parisiLastAbsorbed qs hm hξ hq hqlast
  have hS : HasDerivAt S (deriv (deriv ξ) 1) 1 :=
    (hξ.hasDeriv_deriv 1 ⟨zero_le_one, le_rfl⟩).sub_const _
  have hd : HasDerivAt (fun u => J (S u))
      (((-(1 - mExt ms r.val) / 2) * parisiQMoment ξ h ms qs r) *
        deriv (deriv ξ) 1) 1 := by
    have hJ' : HasDerivAt J
        ((-(1 - mExt ms r.val) / 2) * parisiQMoment ξ h ms qs r) (S 1) := hJ
    simpa only [Function.comp_def] using hJ'.comp 1 hS
  have hAg : HasLinearGrowth (parisiLogCoshTerminal h) :=
    HasLinearGrowth.of_bounded_deriv (hasDerivAt_parisiLogCoshTerminal h)
      (fun y => (abs_parisiLogCoshTerminalDeriv_lt_one h y).le)
  have hAm : Measurable (parisiLogCoshTerminal h) :=
    measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal h)
  have hAeq : parisiQSuffix ξ h ms qs r = parisiLogCoshTerminal h := by
    unfold parisiQSuffix
    exact coleHopfIterate_eq_terminal_of_eq_zero (by simp [r]) _ _ _
  have hmright : mExt ms (r.val + 1) = 1 :=
    mExt_eq_one_of_le ms (by simp [r])
  have hqright : qExt qs (r.val + 2) = 1 := qExt_of_le qs (by simp [r])
  have heq : ∀ u ∈ Icc (0 : ℝ) 1,
      parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h) = J (S u) := by
    intro u hu
    have hdiff : 0 ≤ deriv ξ 1 - deriv ξ u := sub_nonneg.mpr
      (hξ.strictMonoOn_deriv.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2)
    have hinner : coleHopf 1 (Real.toNNReal (deriv ξ 1 - deriv ξ u))
        (parisiLogCoshTerminal h) =
          fun y => parisiLogCoshTerminal h y + (a - S u) / 2 := by
      funext y
      rw [coleHopf_one_parisiLogCoshTerminal, Real.coe_toNNReal _ hdiff]
      dsimp [a, S]
      ring
    have houter : (fun y => coleHopf (mExt ms r.val) (Real.toNNReal (S u))
        (coleHopf 1 (Real.toNNReal (deriv ξ 1 - deriv ξ u))
          (parisiLogCoshTerminal h)) y) =
        fun y => coleHopf (mExt ms r.val) (Real.toNNReal (S u))
          (parisiLogCoshTerminal h) y + (a - S u) / 2 := by
      rw [hinner]
      funext y
      exact coleHopf_add_const hAg hAm _ _ _ _
    by_cases hk : k = 0
    · subst k
      have hr0 : r = 0 := Fin.eq_zero r
      rw [hr0, parisiX₀_first_qUpdate_eq_split qs hm u]
      rw [show parisiQSuffix ξ h ms qs 0 = parisiLogCoshTerminal h by simpa [hr0] using hAeq]
      rw [show mExt ms 1 = 1 by simpa [hr0] using hmright,
        show qExt qs 2 = 1 by simpa [hr0] using hqright]
      change coleHopf 0 (Real.toNNReal (S u))
        (coleHopf 1 (Real.toNNReal (deriv ξ 1 - deriv ξ u))
          (parisiLogCoshTerminal h)) 0 = _
      rw [hinner, coleHopf_add_const hAg hAm]
      simp [J, w₀, r]
    · have hrpos : 0 < r.val := by simpa [r] using Nat.pos_of_ne_zero hk
      unfold parisiX₀
      rw [parisiVar_qUpdate_before qs r u hrpos]
      dsimp [J]
      rw [show w₀ = parisiVar ξ qs 0 by simp [w₀, ne_of_gt hrpos]]
      apply integral_congr_ae
      filter_upwards [] with z₀
      rw [parisiRecGauss_qUpdate_eq_split qs r hm hrpos u z₀,
        hAeq, hmright, hqright]
      change coleHopfIterate _ _ _
        (fun y => coleHopf (mExt ms r.val) (Real.toNNReal (S u))
          (coleHopf 1 (Real.toNNReal (deriv ξ 1 - deriv ξ u))
            (parisiLogCoshTerminal h)) y) z₀ = _
      rw [houter]
  have hev : (fun u => parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h))
      =ᶠ[nhdsWithin 1 (Iic 1)] fun u => J (S u) := by
    filter_upwards [(eventually_ge_nhds zero_lt_one).filter_mono inf_le_left,
      self_mem_nhdsWithin] with u hu0 hu1
    exact heq u ⟨hu0, hu1⟩
  have hw := hd.hasDerivWithinAt.congr_of_eventuallyEq hev
    (heq 1 ⟨zero_le_one, le_rfl⟩)
  exact hw.congr_deriv (by dsimp [r]; ring)

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

/-- The concrete form of (14.220), obtained from the actual Parisi recursion rather than an
assumed derivative of `parisiX₀`. -/
theorem hasDerivAt_parisiFunctional_qUpdate_concrete
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (hm : ParisiMAdmissible ms) {ξ₂ : ℝ}
    (hξ : HasDerivAt ξ (deriv ξ (qs r)) (qs r))
    (hξ' : HasDerivAt (deriv ξ) ξ₂ (qs r))
    (hleft : deriv ξ (qExt qs r.val) < deriv ξ (qs r))
    (hright : deriv ξ (qs r) < deriv ξ (qExt qs (r.val + 2))) :
    HasDerivAt (fun u => parisiFunctional ξ h ms (qUpdate qs r u))
      ((1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) * ξ₂ *
        (-parisiQMoment ξ h ms qs r + qs r)) (qs r) := by
  apply hasDerivAt_parisiFunctional_qUpdate ms qs r
    (hasDerivAt_parisiX₀_qUpdate qs r hm hξ' hleft hright) hξ hξ'

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

/-- Conditional abstract reduction of Proposition 14.7.5, in the overlap-coordinate API.

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

/-- Proposition 14.7.5 after the endpoint inequalities are known: the moment and every
`parisiX₀` derivative are now the concrete ones from the recursion. -/
theorem parisiQ_strict_chain_and_eq_concrete_moment_of_isMin_of_endpoints
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hmin : IsParisiQMinimizer ξ h ms qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) :
    (∀ n : ℕ, n ≤ k + 1 → qExt qs n < qExt qs (n + 1)) ∧
      ∀ r, qs r = parisiQMoment ξ h ms qs r := by
  have hchain : ∀ n : ℕ, n ≤ k + 1 → qExt qs n < qExt qs (n + 1) :=
    fun n hn => qExt_strict_succ hmin.1.1 hq0 hq1 hn
  refine ⟨hchain, ?_⟩
  intro r
  have hqpos : 0 < qs r := hq0.trans_le (hmin.1.monotone (Fin.zero_le r))
  have hqmem := hmin.1.mem_Icc r
  have hξ₂pos : 0 < deriv (deriv ξ) (qs r) :=
    hξ.second_pos _ hqmem (ne_of_gt hqpos)
  have hleftq : qExt qs r.val < qs r := by
    simpa [qExt_succ_of_lt qs r.isLt] using hchain r.val (by omega)
  have hrightq : qs r < qExt qs (r.val + 2) := by
    simpa [qExt_succ_of_lt qs r.isLt] using hchain (r.val + 1) (by omega)
  have hleft : deriv ξ (qExt qs r.val) < deriv ξ (qs r) :=
    hξ.strictMonoOn_deriv (qExt_mem_Icc hmin.1.monotone hmin.1.2.1 hmin.1.2.2 _)
      hqmem hleftq
  have hright : deriv ξ (qs r) < deriv ξ (qExt qs (r.val + 2)) :=
    hξ.strictMonoOn_deriv hqmem
      (qExt_mem_Icc hmin.1.monotone hmin.1.2.1 hmin.1.2.2 _) hrightq
  apply parisiQ_eq_moment_of_isLocalMin_of_admissible ms qs r hm hξ₂pos
    (hmin.isLocalMin_qUpdate ms qs hq0 hq1 r)
  · change HasDerivAt
      (fun u => parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h))
      ((-1 / 2 : ℝ) * deriv (deriv ξ) (qs r) *
        (mExt ms (r.val + 1) - mExt ms r.val) * parisiQMoment ξ h ms qs r) (qs r)
    exact hasDerivAt_parisiX₀_qUpdate qs r hm
      (hξ.hasDeriv_deriv _ hqmem) hleft hright
  · exact hξ.hasDeriv _ hqmem
  · exact hξ.hasDeriv_deriv _ hqmem

lemma hasDerivAt_linear_right_extension {f : ℝ → ℝ} {b d : ℝ}
    (hf : HasDerivWithinAt f d (Iic b) b) :
    HasDerivAt (fun u => if u ≤ b then f u else f b + (u - b) * d) d b := by
  let E : ℝ → ℝ := fun u => if u ≤ b then f u else f b + (u - b) * d
  have hl : HasDerivWithinAt E d (Iic b) b :=
    hf.congr_of_eventuallyEq
      (by
        filter_upwards [self_mem_nhdsWithin] with u hu
        change u ≤ b at hu
        simp [E, hu])
      (by simp [E])
  have ha : HasDerivAt (fun u => f b + (u - b) * d) d b := by
    simpa using (((hasDerivAt_id b).sub_const b).mul_const d).const_add (f b)
  have hr : HasDerivWithinAt E d (Ici b) b :=
    ha.hasDerivWithinAt.congr_of_eventuallyEq
      (by
        filter_upwards [self_mem_nhdsWithin] with u hu
        by_cases hub : u ≤ b
        · have hueq : u = b := le_antisymm hub hu
          simp [E, hueq]
        · simp [E, hub])
      (by simp [E])
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr

/-! ### I.i.d. random external fields -/

/-- A dominated left derivative can be averaged by extending each integrand linearly to the
right.  This extension is only an auxiliary function; the conclusion concerns the original
integral on its admissible left half-line. -/
theorem hasDerivWithinAt_integral_of_dominated_left
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f D : ℝ → α → ℝ} {d bound : α → ℝ} {a b : ℝ} (hab : a < b)
    (hfm : ∀ u, Measurable (f u)) (hfi : Integrable (f b) μ)
    (hdm : Measurable d) (hbi : Integrable bound μ)
    (hDb : ∀ x, ∀ u ∈ Ioo a b, ‖D u x‖ ≤ bound x)
    (hdb : ∀ x, ‖d x‖ ≤ bound x)
    (hD : ∀ x, ∀ u ∈ Ioo a b, HasDerivAt (fun v => f v x) (D u x) u)
    (hd : ∀ x, HasDerivWithinAt (fun u => f u x) (d x) (Iic b) b) :
    HasDerivWithinAt (fun u => ∫ x, f u x ∂μ) (∫ x, d x ∂μ) (Iic b) b := by
  let E : ℝ → α → ℝ := fun u x =>
    if u ≤ b then f u x else f b x + (u - b) * d x
  let DE : ℝ → α → ℝ := fun u x => if u < b then D u x else d x
  have hEm : ∀ u, Measurable (E u) := by
    intro u
    by_cases hu : u ≤ b
    · simpa only [E, if_pos hu] using hfm u
    · simp only [E, if_neg hu]
      exact (hfm b).add (hdm.const_mul (u - b))
  have hEi : Integrable (E b) μ := by simpa [E] using hfi
  have hDEm : Measurable (DE b) := by simpa [DE] using hdm
  have hDEb : ∀ᵐ x ∂μ, ∀ u ∈ Ioo a (b + 1), ‖DE u x‖ ≤ bound x := by
    filter_upwards [] with x
    intro u hu
    by_cases hub : u < b
    · simpa [DE, hub] using hDb x u ⟨hu.1, hub⟩
    · simpa [DE, hub] using hdb x
  have hEd : ∀ᵐ x ∂μ, ∀ u ∈ Ioo a (b + 1),
      HasDerivAt (fun v => E v x) (DE u x) u := by
    filter_upwards [] with x
    intro u hu
    rcases lt_trichotomy u b with hub | rfl | hbu
    · have heq : (fun v => E v x) =ᶠ[nhds u] fun v => f v x := by
        filter_upwards [eventually_lt_nhds hub] with v hv
        simp [E, hv.le]
      simpa [DE, hub] using (hD x u ⟨hu.1, hub⟩).congr_of_eventuallyEq heq
    · simpa [E, DE] using hasDerivAt_linear_right_extension (hd x)
    · have haff : HasDerivAt (fun v => f b x + (v - b) * d x) (d x) u := by
        simpa using (((hasDerivAt_id u).sub_const b).mul_const (d x)).const_add (f b x)
      have heq : (fun v => E v x) =ᶠ[nhds u]
          fun v => f b x + (v - b) * d x := by
        filter_upwards [eventually_gt_nhds hbu] with v hv
        simp [E, not_le.mpr hv]
      simpa [DE, not_lt.mpr hbu.le] using haff.congr_of_eventuallyEq heq
  have hfull := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds hab (by linarith : b < b + 1))
    (Filter.Eventually.of_forall fun u => (hEm u).aestronglyMeasurable) hEi
    hDEm.aestronglyMeasurable hDEb hbi hEd).2
  have heq : (fun u => ∫ x, f u x ∂μ) =ᶠ[nhdsWithin b (Iic b)]
      fun u => ∫ x, E u x ∂μ := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    change u ≤ b at hu
    simp [E, hu]
  simpa only [DE, lt_self_iff_false, if_false] using
    hfull.hasDerivWithinAt.congr_of_eventuallyEq heq (by simp [E])

/-- The book-level moment after averaging the common site variable against its probability
law. -/
noncomputable def randomFieldParisiQMoment (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) : ℝ :=
  ∫ h, parisiQMoment ξ h ms qs r ∂μh

/-- The concrete moment is measurable in the external-field coordinate. -/
theorem measurable_parisiQMoment_externalField {ξ : ℝ → ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hm : ParisiMAdmissible ms) :
    Measurable fun h => parisiQMoment ξ h ms qs r := by
  obtain ⟨hA, C, hA', hA''c, hA'b, hA''b⟩ :=
    parisiQSuffix_deriv_regular (ξ := ξ) (h := 0) qs r hm
  let A : ℝ → ℝ := parisiQSuffix ξ 0 ms qs r
  let A' : ℝ → ℝ := parisiQSuffixDeriv ξ 0 ms qs r
  let vR : ℝ≥0 := Real.toNNReal
    (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r))
  let vL : ℝ≥0 := Real.toNNReal
    (deriv ξ (qs r) - deriv ξ (qExt qs r.val))
  let f : ℝ → ℝ := coleHopfSplitMoment (mExt ms (r.val + 1))
    (mExt ms r.val) vR vL A A'
  let B : ℝ → ℝ := coleHopf (mExt ms (r.val + 1)) vR A
  let G : ℝ → ℝ := coleHopf (mExt ms r.val) vL B
  have hfc : Continuous f := continuous_coleHopfSplitMoment hA hA' hA'b
  have hAm : Measurable A := measurable_of_hasDerivAt hA
  have hAlip : ∀ x y, |A y - A x| ≤ 1 * |y - x| :=
    ProbabilityTheory.abs_sub_le_mul_abs_sub_of_hasDerivAt hA hA'b
  have hBlip : ∀ x y, |B y - B x| ≤ 1 * |y - x| :=
    abs_coleHopf_sub_le_of_lipschitz _ hAm hAlip _
  have hBm : Measurable B :=
    (lipschitzWith_toNNReal_of_abs_sub_le hBlip).continuous.measurable
  have hGlip : ∀ x y, |G y - G x| ≤ 1 * |y - x| :=
    abs_coleHopf_sub_le_of_lipschitz _ hBm hBlip _
  have hGm : Measurable G :=
    (lipschitzWith_toNNReal_of_abs_sub_le hGlip).continuous.measurable
  have hfh (h x : ℝ) :
      coleHopfSplitMoment (mExt ms (r.val + 1)) (mExt ms r.val) vR vL
          (parisiQSuffix ξ h ms qs r) (parisiQSuffixDeriv ξ h ms qs r) x =
        f (h + x) := by
    have hAt : parisiQSuffix ξ h ms qs r = fun y => A (h + y) := by
      funext y
      exact parisiQSuffix_translate ξ h ms qs r y
    have hA't : parisiQSuffixDeriv ξ h ms qs r = fun y => A' (h + y) := by
      funext y
      exact parisiQSuffixDeriv_translate ξ h ms qs r y
    rw [hAt, hA't]
    exact coleHopfSplitMoment_translate _ _ _ _ A A' h x
  have hGh (h x : ℝ) :
      coleHopf (mExt ms r.val) vL
          (coleHopf (mExt ms (r.val + 1)) vR (parisiQSuffix ξ h ms qs r)) x =
        G (h + x) := by
    have hAt : parisiQSuffix ξ h ms qs r = fun y => A (h + y) := by
      funext y
      exact parisiQSuffix_translate ξ h ms qs r y
    rw [hAt]
    have hinner : coleHopf (mExt ms (r.val + 1)) vR (fun y => A (h + y)) =
        fun y => B (h + y) := by
      funext y
      exact coleHopf_translate _ _ A h y
    rw [hinner]
    exact coleHopf_translate _ _ B h x
  by_cases hr : r.val = 0
  · have heq : (fun h => parisiQMoment ξ h ms qs r) = fun h => f h := by
      funext h
      unfold parisiQMoment
      rw [if_pos hr]
      simpa [vR, vL] using hfh h 0
    rw [heq]
    exact hfc.measurable
  · have hprefix_pos : ∀ p, 0 < parisiQPrefixMasses ms r p := fun p =>
      hm.mExt_pos (by simp [parisiQPrefixMasses])
    have hprefix_le : ∀ p, parisiQPrefixMasses ms r p ≤ 1 := fun p =>
      mExt_le_one (fun i => (hm.2.2 i).le) _
    let F : ℝ → ℝ := fun y =>
      ∫ zs, f (y + ∑ p, zs p)
        ∂cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
          (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
          (fun zs => ENNReal.ofReal (Real.exp (G (y + ∑ p, zs p))))
    have hFm : Measurable F :=
      measurable_integral_cascadeTiltMeasure_comp_add_sum
        (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
        hprefix_pos hprefix_le hGm hGlip hfc.measurable
    have heq : (fun h => parisiQMoment ξ h ms qs r) =
        fun h => ∫ z₀, F (h + z₀) ∂gaussianReal 0 (parisiVar ξ qs 0) := by
      funext h
      unfold parisiQMoment
      rw [if_neg hr]
      apply integral_congr_ae
      filter_upwards [] with z₀
      change (∫ zs, coleHopfSplitMoment (mExt ms (r.val + 1))
          (mExt ms r.val) vR vL (parisiQSuffix ξ h ms qs r)
            (parisiQSuffixDeriv ξ h ms qs r) (z₀ + ∑ p, zs p)
        ∂cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
          (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
          (fun zs => ENNReal.ofReal (Real.exp
            (coleHopf (mExt ms r.val) vL
              (coleHopf (mExt ms (r.val + 1)) vR
                (parisiQSuffix ξ h ms qs r)) (z₀ + ∑ p, zs p))))) = F (h + z₀)
      unfold F
      have hmeasure :
          cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
            (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
            (fun zs => ENNReal.ofReal (Real.exp
              (coleHopf (mExt ms r.val) vL
                (coleHopf (mExt ms (r.val + 1)) vR
                  (parisiQSuffix ξ h ms qs r)) (z₀ + ∑ p, zs p)))) =
          cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
            (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
            (fun zs => ENNReal.ofReal (Real.exp (G (h + z₀ + ∑ p, zs p)))) := by
        congr 1
        funext zs
        rw [hGh]
        apply congrArg ENNReal.ofReal
        apply congrArg Real.exp
        apply congrArg G
        ring
      rw [hmeasure]
      apply integral_congr_ae
      filter_upwards [] with zs
      rw [hfh]
      congr 1
      ring
    rw [heq]
    exact (hFm.comp (measurable_fst.add measurable_snd)).stronglyMeasurable
      |>.integral_prod_right'.measurable

theorem integrable_parisiQMoment_externalField {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (hm : ParisiMAdmissible ms) :
    Integrable (fun h => parisiQMoment ξ h ms qs r) μh :=
  Integrable.of_bound (measurable_parisiQMoment_externalField qs r hm).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs]
      exact abs_parisiQMoment_le_one qs r hm)

/-- Talagrand's nondegeneracy condition for the external-field law, in the form
`$0 < \mathbb E h^2 < \infty$`. -/
structure NondegenerateExternalFieldLaw (μh : Measure ℝ) : Prop where
  sq_integrable : Integrable (fun h : ℝ => h ^ 2) μh
  second_moment_pos : 0 < ∫ h, h ^ 2 ∂μh

/-- At a zero first overlap, the first moment is a continuous function of the external field. -/
theorem continuous_parisiQMoment_first_of_eq_zero {ξ : ℝ → ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hqzero : qs 0 = 0) :
    Continuous fun h => parisiQMoment ξ h ms qs 0 := by
  have hlevelpos : ∀ i, 0 < parisiLevelMasses ms i := by
    intro i
    rw [parisiLevelMasses_apply]
    exact hm.mExt_pos (by omega)
  let B' : ℝ → ℝ := coleHopfIterateDeriv (k + 1) (parisiLevelMasses ms)
    (parisiLevelVars ξ qs) (parisiLogCoshTerminal 0)
    (parisiLogCoshTerminalDeriv 0)
  obtain ⟨hB, C, hB', hB''c, hB'b, hB''b⟩ :=
    coleHopfIterate_deriv_regular (parisiLevelMasses ms) (parisiLevelVars ξ qs)
      (hasDerivAt_parisiLogCoshTerminal 0)
      (hasDerivAt_parisiLogCoshTerminalDeriv 0)
      (continuous_parisiLogCoshTerminalDeriv2 0)
      (fun x => (abs_parisiLogCoshTerminalDeriv_lt_one 0 x).le)
      (abs_parisiLogCoshTerminalDeriv2_le_one 0) hlevelpos
  have hB'c : Continuous B' :=
    continuous_iff_continuousAt.2 fun x => (hB' x).continuousAt
  have heq : (fun h => parisiQMoment ξ h ms qs 0) = fun h => B' h ^ 2 := by
    funext h
    rw [parisiQMoment_first_eq_sq_full_deriv ms qs hqzero,
      coleHopfIterateDeriv_parisiLogCoshTerminal_translate
        (parisiLevelMasses ms) (parisiLevelVars ξ qs) hlevelpos h]
  rw [heq]
  exact hB'c.pow 2

/-- Averaging over the site law preserves continuity of the first moment at the collapsed
variance endpoint. -/
theorem continuousAt_randomFieldParisiQMoment_first_qUpdate_zero
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ}
    (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) :
    ContinuousAt
      (fun u => randomFieldParisiQMoment μh ξ ms (qUpdate qs 0 u) 0) 0 := by
  unfold randomFieldParisiQMoment
  exact continuousAt_of_dominated
    (Filter.Eventually.of_forall fun u =>
      (measurable_parisiQMoment_externalField (qUpdate qs 0 u) 0 hm).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u =>
      Filter.Eventually.of_forall fun h => by
        rw [Real.norm_eq_abs]
        exact abs_parisiQMoment_le_one (qUpdate qs 0 u) 0 hm)
    (integrable_const (μ := μh) (1 : ℝ))
    (Filter.Eventually.of_forall fun h =>
      continuousAt_parisiQMoment_first_qUpdate_zero qs hm hξ)

/-- The nondegenerate site law makes the averaged first moment strictly positive. -/
theorem randomFieldParisiQMoment_first_pos {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hqzero : qs 0 = 0)
    (hμ : NondegenerateExternalFieldLaw μh) :
    0 < randomFieldParisiQMoment μh ξ ms qs 0 := by
  have hmm : Measurable fun h => parisiQMoment ξ h ms qs 0 :=
    (continuous_parisiQMoment_first_of_eq_zero qs hm hqzero).measurable
  have hmi : Integrable (fun h => parisiQMoment ξ h ms qs 0) μh :=
    Integrable.of_bound hmm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun h => by
        rw [Real.norm_eq_abs]
        exact abs_parisiQMoment_le_one qs 0 hm)
  have hsuppSq : 0 < μh (Function.support fun h : ℝ => h ^ 2) := by
    rw [← integral_pos_iff_support_of_nonneg (fun h => sq_nonneg h) hμ.sq_integrable]
    exact hμ.second_moment_pos
  have hsubset : Function.support (fun h : ℝ => h ^ 2) ⊆
      Function.support (fun h => parisiQMoment ξ h ms qs 0) := by
    intro h hh
    have hh0 : h ≠ 0 := by
      intro heq
      apply hh
      simp [heq]
    exact ne_of_gt (parisiQMoment_first_pos_of_ne_zero qs hm hqzero hh0)
  unfold randomFieldParisiQMoment
  rw [integral_pos_iff_support_of_nonneg
    (fun h => parisiQMoment_nonneg ξ h ms qs 0) hmi]
  exact hsuppSq.trans_le (measure_mono hsubset)

/-- At a final overlap equal to one, the averaged final moment is strictly below one. -/
theorem randomFieldParisiQMoment_last_lt_one {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hqlast : qs (Fin.last k) = 1) :
    randomFieldParisiQMoment μh ξ ms qs (Fin.last k) < 1 := by
  unfold randomFieldParisiQMoment
  apply integral_lt_one_of_measurable_of_lt
  · exact measurable_parisiQMoment_externalField qs (Fin.last k) hm
  · exact fun h => abs_parisiQMoment_le_one qs (Fin.last k) hm
  · exact fun h => parisiQMoment_last_lt_one qs hm hqlast

/-- The averaged concrete moment is the same expectation of any product-coordinate of the
i.i.d. external-field vector. -/
theorem randomFieldParisiQMoment_eq_integral_externalFieldVec_apply
    {N : ℕ} (i : Fin N) {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (hm : ParisiMAdmissible ms) :
    randomFieldParisiQMoment μh ξ ms qs r =
      ∫ hVec, parisiQMoment ξ (hVec i) ms qs r ∂externalFieldVecLaw N μh := by
  unfold randomFieldParisiQMoment
  exact (integral_externalFieldVec_apply N μh i
    (fun h => parisiQMoment ξ h ms qs r)
    (measurable_parisiQMoment_externalField qs r hm).aestronglyMeasurable).symm

/-- The averaged `X₀` is obtained by sampling any coordinate of the i.i.d. external-field
vector. -/
theorem randomFieldParisiX₀_eq_integral_externalFieldVec_apply
    {N : ℕ} (i : Fin N) {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1) :
    randomFieldParisiX₀ μh ξ ms qs =
      ∫ hVec, parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (hVec i + x)))
        ∂externalFieldVecLaw N μh := by
  unfold randomFieldParisiX₀
  exact (integral_externalFieldVec_apply N μh i
    (fun h => parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x))))
    (measurable_parisiX₀_logCosh ξ ms qs hpos hle).aestronglyMeasurable).symm

/-- The law-level Parisi functional is the expectation obtained by sampling any one coordinate
of the i.i.d. external-field vector.  Thus the thermodynamic functional depends on the common
site law, rather than on the number of sampled sites or the chosen coordinate. -/
theorem randomFieldParisiFunctional_eq_integral_externalFieldVec_apply
    {N : ℕ} (i : Fin N) {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1) :
    randomFieldParisiFunctional μh ξ ms qs =
      ∫ hVec, parisiFunctional ξ (hVec i) ms qs ∂externalFieldVecLaw N μh := by
  rw [randomFieldParisiFunctional_eq_integral hμh ξ ms qs hpos hle]
  exact (integral_externalFieldVec_apply N μh i
    (fun h => parisiFunctional ξ h ms qs)
    (integrable_parisiFunctional_externalField hμh ξ ms qs hpos hle).aestronglyMeasurable).symm

/-- Differentiate the averaged `X₀` after supplying a common local integrable bound for the
fixed-field derivatives.  This is the measure-theoretic bridge from the pointwise split
derivative to the moment averaged over the common i.i.d. site law. -/
theorem hasDerivAt_randomFieldParisiX₀_qUpdate_of_dominated
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) {q : ℝ}
    {D : ℝ → ℝ → ℝ} {bound : ℝ → ℝ} {s : Set ℝ}
    (hs : s ∈ nhds q)
    (hF_meas : ∀ᶠ u in nhds q, AEStronglyMeasurable
      (fun h => parisiX₀ ξ ms (qUpdate qs r u)
        (fun x => Real.log (Real.cosh (h + x)))) μh)
    (hF_int : Integrable
      (fun h => parisiX₀ ξ ms (qUpdate qs r q)
        (fun x => Real.log (Real.cosh (h + x)))) μh)
    (hD_meas : AEStronglyMeasurable (D q) μh)
    (hbound : ∀ᵐ h ∂μh, ∀ u ∈ s, ‖D u h‖ ≤ bound h)
    (hbound_int : Integrable bound μh)
    (hdiff : ∀ᵐ h ∂μh, ∀ u ∈ s, HasDerivAt
      (fun v => parisiX₀ ξ ms (qUpdate qs r v)
        (fun x => Real.log (Real.cosh (h + x)))) (D u h) u) :
    HasDerivAt (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
      (∫ h, D q h ∂μh) q := by
  unfold randomFieldParisiX₀
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hD_meas
    hbound hbound_int hdiff).2

/-- Differentiation under the external-field integral, with the domination and measurability
hypotheses discharged by the concrete recursion and the named condition on `$ξ$`. -/
theorem hasDerivAt_randomFieldParisiX₀_qUpdate_concrete
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hμh : Integrable (fun h : ℝ => h) μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs)
    (hleftq : qExt qs r.val < qs r) (hrightq : qs r < qExt qs (r.val + 2)) :
    HasDerivAt (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
      ((-1 / 2 : ℝ) * deriv (deriv ξ) (qs r) *
        (mExt ms (r.val + 1) - mExt ms r.val) *
          randomFieldParisiQMoment μh ξ ms qs r) (qs r) := by
  let qL : ℝ := qExt qs r.val
  let qR : ℝ := qExt qs (r.val + 2)
  let gap : ℝ := mExt ms (r.val + 1) - mExt ms r.val
  let D : ℝ → ℝ → ℝ := fun u h =>
    (-1 / 2 : ℝ) * deriv (deriv ξ) u * gap *
      parisiQMoment ξ h ms (qUpdate qs r u) r
  let K : ℝ := (1 / 2 : ℝ) * gap * deriv (deriv ξ) 1
  have hqLmem : qL ∈ Icc (0 : ℝ) 1 := by
    exact qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _
  have hqRmem : qR ∈ Icc (0 : ℝ) 1 := by
    exact qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _
  have hqmem : qs r ∈ Icc (0 : ℝ) 1 := hq.mem_Icc r
  have hs : Ioo qL qR ∈ nhds (qs r) := Ioo_mem_nhds hleftq hrightq
  have hFmeas : ∀ᶠ u in nhds (qs r), AEStronglyMeasurable
      (fun h => parisiX₀ ξ ms (qUpdate qs r u)
        (fun x => Real.log (Real.cosh (h + x)))) μh :=
    Filter.Eventually.of_forall fun u =>
      (measurable_parisiX₀_logCosh ξ ms (qUpdate qs r u)
        hm.2.1 (fun p => (hm.2.2 p).le)).aestronglyMeasurable
  have hFint : Integrable
      (fun h => parisiX₀ ξ ms (qUpdate qs r (qs r))
        (fun x => Real.log (Real.cosh (h + x)))) μh := by
    have heq : qUpdate qs r (qs r) = qs := by
      funext p
      by_cases hp : p = r
      · subst p
        simp
      · simp [qUpdate, hp]
    rw [heq]
    exact integrable_parisiX₀_logCosh hμh ξ ms qs hm.2.1 (fun p => (hm.2.2 p).le)
  have hDmeas : AEStronglyMeasurable (D (qs r)) μh := by
    have hmom := measurable_parisiQMoment_externalField (ξ := ξ)
      (qUpdate qs r (qs r)) r hm
    simpa [D] using
      (hmom.const_mul ((-1 / 2 : ℝ) * deriv (deriv ξ) (qs r) * gap)).aestronglyMeasurable
  have hbound : ∀ᵐ h ∂μh, ∀ u ∈ Ioo qL qR, ‖D u h‖ ≤ K := by
    filter_upwards [] with h
    intro u hu
    have humem : u ∈ Ioc (0 : ℝ) 1 :=
      ⟨hqLmem.1.trans_lt hu.1, hu.2.le.trans hqRmem.2⟩
    have hsecpos : 0 < deriv (deriv ξ) u :=
      hξ.second_pos u ⟨humem.1.le, humem.2⟩ (ne_of_gt humem.1)
    have hsecle : deriv (deriv ξ) u ≤ deriv (deriv ξ) 1 :=
      hξ.monotoneOn_second humem ⟨zero_lt_one, le_rfl⟩ humem.2
    have hgap : 0 < gap := hm.mExt_gap_pos r
    have hM := abs_parisiQMoment_le_one (ξ := ξ) (h := h) (qUpdate qs r u) r hm
    have hhalf : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
    dsimp [D, K]
    rw [abs_mul, abs_mul, abs_mul, hhalf,
      abs_of_nonneg hsecpos.le, abs_of_nonneg hgap.le]
    calc
      1 / 2 * deriv (deriv ξ) u * gap *
          |parisiQMoment ξ h ms (qUpdate qs r u) r| ≤
          1 / 2 * deriv (deriv ξ) u * gap * 1 := by gcongr
      _ ≤ 1 / 2 * deriv (deriv ξ) 1 * gap * 1 := by gcongr
      _ = 1 / 2 * gap * deriv (deriv ξ) 1 := by ring
  have hboundInt : Integrable (fun _ : ℝ => K) μh := integrable_const K
  have hdiff : ∀ᵐ h ∂μh, ∀ u ∈ Ioo qL qR, HasDerivAt
      (fun v => parisiX₀ ξ ms (qUpdate qs r v)
        (fun x => Real.log (Real.cosh (h + x)))) (D u h) u := by
    filter_upwards [] with h
    intro u hu
    let qu := qUpdate qs r u
    have humem : u ∈ Icc (0 : ℝ) 1 :=
      ⟨hqLmem.1.trans (hu.1.le), hu.2.le.trans hqRmem.2⟩
    have hquself : qu r = u := qUpdate_self qs r u
    have hquleft : qExt qu r.val = qL := by
      exact qExt_qUpdate_of_lt qs r u (by omega)
    have hquright : qExt qu (r.val + 2) = qR := by
      exact qExt_qUpdate_of_gt qs r u (by omega)
    have hleft : deriv ξ (qExt qu r.val) < deriv ξ (qu r) := by
      rw [hquleft, hquself]
      exact hξ.strictMonoOn_deriv hqLmem humem hu.1
    have hright : deriv ξ (qu r) < deriv ξ (qExt qu (r.val + 2)) := by
      rw [hquself, hquright]
      exact hξ.strictMonoOn_deriv humem hqRmem hu.2
    have hξderiv := hξ.hasDeriv_deriv u humem
    rw [← hquself] at hξderiv
    have hd := hasDerivAt_parisiX₀_qUpdate (ξ := ξ) (h := h)
      qu r hm hξderiv hleft hright
    have hupdate : (fun v => qUpdate qu r v) = fun v => qUpdate qs r v := by
      funext v
      funext p
      simp [qu, qUpdate]
    have hfun :
        (fun v => parisiX₀ ξ ms (qUpdate qu r v)
          (parisiLogCoshTerminal h)) =
        fun v => parisiX₀ ξ ms (qUpdate qs r v)
          (parisiLogCoshTerminal h) := by
      funext v
      rw [congrFun hupdate v]
    rw [hfun] at hd
    change HasDerivAt
      (fun v => parisiX₀ ξ ms (qUpdate qs r v) (parisiLogCoshTerminal h)) (D u h) u
    simpa [D, gap, qu, hquself] using hd
  have hd := hasDerivAt_randomFieldParisiX₀_qUpdate_of_dominated
    ms qs r hs hFmeas hFint hDmeas hbound hboundInt hdiff
  have hqsupdate : qUpdate qs r (qs r) = qs := by
    funext p
    simp [qUpdate]
  convert hd using 1
  unfold D randomFieldParisiQMoment gap
  rw [hqsupdate]
  rw [← integral_const_mul]

/-- No admissible overlap vector lowers the random-field Parisi functional when the mass
parameters and the common i.i.d. site law are fixed. -/
def IsRandomFieldParisiQMinimizer (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) : Prop :=
  ParisiQAdmissible qs ∧
    ∀ qs', ParisiQAdmissible qs' →
      randomFieldParisiFunctional μh ξ ms qs ≤ randomFieldParisiFunctional μh ξ ms qs'

/-- Admissible random-field minimization gives the constrained one-coordinate comparison. -/
lemma IsRandomFieldParisiQMinimizer.le_qUpdate
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ}
    {qs : Fin (k + 1) → ℝ} (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    (r : Fin (k + 1)) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hleft : ∀ p, p < r → qs p < u) (hright : ∀ p, r < p → u < qs p) :
    randomFieldParisiFunctional μh ξ ms qs ≤
      randomFieldParisiFunctional μh ξ ms (qUpdate qs r u) :=
  hmin.2 _ (hmin.1.qUpdate r hu0 hu1 hleft hright)

/-- Strict endpoint inequalities turn a global random-field minimizer into a local minimum
along each overlap coordinate. -/
lemma IsRandomFieldParisiQMinimizer.isLocalMin_qUpdate
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) (r : Fin (k + 1)) :
    IsLocalMin (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u))
      (qs r) := by
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
      randomFieldParisiFunctional μh ξ ms qs ≤
        randomFieldParisiFunctional μh ξ ms (qUpdate qs r u) := by
    filter_upwards [hu0, hu1, hleft, hright] with u hu0 hu1 hleft hright
    exact hmin.le_qUpdate r hu0 hu1 hleft hright
  change ∀ᶠ u in nhds (qs r),
    randomFieldParisiFunctional μh ξ ms (qUpdate qs r (qs r)) ≤
      randomFieldParisiFunctional μh ξ ms (qUpdate qs r u)
  simpa [qUpdate] using hle

/-- At the lower endpoint, constrained random-field minimality forces a nonnegative right
derivative. -/
lemma IsRandomFieldParisiQMinimizer.first_deriv_nonneg
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ}
    {qs : Fin (k + 1) → ℝ} (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    (hq0 : qs 0 = 0) {d : ℝ}
    (hd : HasDerivAt
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs 0 u)) d (qs 0)) :
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
  have hlocal : IsLocalMinOn
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs 0 u))
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

/-- At the upper endpoint, constrained random-field minimality forces a nonpositive left
derivative. -/
lemma IsRandomFieldParisiQMinimizer.last_derivWithin_nonpos
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ}
    {qs : Fin (k + 1) → ℝ} (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    (hq1 : qs (Fin.last k) = 1) {d : ℝ}
    (hd : HasDerivWithinAt
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs (Fin.last k) u)) d
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
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs (Fin.last k) u))
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

/-- The full-derivative version of the constrained endpoint sign lemma. -/
lemma IsRandomFieldParisiQMinimizer.last_deriv_nonpos
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ}
    {qs : Fin (k + 1) → ℝ} (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    (hq1 : qs (Fin.last k) = 1) {d : ℝ}
    (hd : HasDerivAt
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs (Fin.last k) u)) d
      (qs (Fin.last k))) : d ≤ 0 :=
  hmin.last_derivWithin_nonpos hq1 hd.hasDerivWithinAt

/-- The random-field theta-sum written over the free overlap coordinates. -/
theorem randomFieldParisiFunctional_eq_theta_fin_sum (μh : Measure ℝ) (ξ : ℝ → ℝ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    randomFieldParisiFunctional μh ξ ms qs
      = Real.log 2 + randomFieldParisiX₀ μh ξ ms qs
        + (1 / 2) * ∑ p : Fin (k + 1),
            parisiTheta ξ (qs p) * (mExt ms (p.val + 1) - mExt ms p.val)
        - (1 / 2) * parisiTheta ξ 1 := by
  rw [randomFieldParisiFunctional_eq_theta_sum]
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

/-- Along one overlap coordinate, the random-field functional is its averaged `X₀` plus the
same theta term as in the deterministic-field functional. -/
theorem randomFieldParisiFunctional_qUpdate_eq (μh : Measure ℝ) (ξ : ℝ → ℝ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (u : ℝ) :
    randomFieldParisiFunctional μh ξ ms (qUpdate qs r u)
      = parisiQConst ξ ms qs r
        + (randomFieldParisiX₀ μh ξ ms (qUpdate qs r u)
          + (1 / 2) * (mExt ms (r.val + 1) - mExt ms r.val) * parisiTheta ξ u) := by
  classical
  rw [randomFieldParisiFunctional_eq_theta_fin_sum]
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

/-- The averaged concrete recursion is continuous along every admissible overlap variation,
including variations based at zero or one. -/
theorem continuousWithinAt_randomFieldParisiX₀_qUpdate
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs) :
    ContinuousWithinAt
      (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
      (Icc (0 : ℝ) 1) (qs r) := by
  have hqmem : qs r ∈ Icc (0 : ℝ) 1 := hq.mem_Icc r
  have hdu : Filter.Tendsto (fun u => deriv ξ u)
      (nhdsWithin (qs r) (Icc (0 : ℝ) 1)) (nhds (deriv ξ (qs r))) :=
    hξ.deriv_continuous (qs r) hqmem
  have hunif := tendsto_uniform_parisiX₀_qUpdate qs r id hm hdu
  have hsame : qUpdate qs r (qs r) = qs := by
    funext p
    by_cases hp : p = r
    · subst p
      simp
    · simp [qUpdate, hp]
  show Filter.Tendsto
    (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
    (nhdsWithin (qs r) (Icc (0 : ℝ) 1))
    (nhds (randomFieldParisiX₀ μh ξ ms (qUpdate qs r (qs r))))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  filter_upwards [hunif (ε / 2) hhalf] with u hu
  unfold randomFieldParisiX₀
  rw [dist_eq, hsame, ← integral_sub
    (integrable_parisiX₀_logCosh hμh ξ ms (qUpdate qs r u)
      hm.2.1 (fun p => (hm.2.2 p).le))
    (integrable_parisiX₀_logCosh hμh ξ ms qs
      hm.2.1 (fun p => (hm.2.2 p).le))]
  have hb := norm_integral_le_of_norm_le_const
    (μ := μh)
    (f := fun h =>
      parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h) -
        parisiX₀ ξ ms qs (parisiLogCoshTerminal h))
    (C := ε / 2) (Filter.Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs]
      simpa only [id_eq, hsame] using (hu h).le)
  rw [Real.norm_eq_abs] at hb
  have hb' :
      |∫ h,
          (parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h) -
            parisiX₀ ξ ms qs (parisiLogCoshTerminal h)) ∂μh| ≤ ε / 2 := by
    simpa using hb
  exact hb'.trans_lt (half_lt_self hε)

/-- The random-field Parisi functional is continuous at constrained overlap endpoints. -/
theorem continuousWithinAt_randomFieldParisiFunctional_qUpdate
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs) :
    ContinuousWithinAt
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u))
      (Icc (0 : ℝ) 1) (qs r) := by
  let C : ℝ := parisiQConst ξ ms qs r
  let c : ℝ := (1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val)
  have hX := continuousWithinAt_randomFieldParisiX₀_qUpdate ms qs r hμh hm hξ hq
  have hqmem : qs r ∈ Icc (0 : ℝ) 1 := hq.mem_Icc r
  have hθ : ContinuousAt (parisiTheta ξ) (qs r) :=
    (hasDerivAt_parisiTheta (hξ.hasDeriv _ hqmem)
      (hξ.hasDeriv_deriv _ hqmem)).continuousAt
  have hright : ContinuousWithinAt
      (fun u => C + (randomFieldParisiX₀ μh ξ ms (qUpdate qs r u) +
        c * parisiTheta ξ u)) (Icc (0 : ℝ) 1) (qs r) :=
    continuousWithinAt_const.add (hX.add
      (continuousWithinAt_const.mul hθ.continuousWithinAt))
  have hfun :
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u)) =
        fun u => C + (randomFieldParisiX₀ μh ξ ms (qUpdate qs r u) +
          c * parisiTheta ξ u) := by
    funext u
    exact randomFieldParisiFunctional_qUpdate_eq μh ξ ms qs r u
  rw [hfun]
  exact hright

/-- The random-field version of (14.220).  The moment `M` includes the expectation over the
common law of an i.i.d. external-field coordinate. -/
theorem hasDerivAt_randomFieldParisiFunctional_qUpdate
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) {q ξ₂ M : ℝ}
    (hX₀ : HasDerivAt
      (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
      ((-1 / 2 : ℝ) * ξ₂ * (mExt ms (r.val + 1) - mExt ms r.val) * M) q)
    (hξ : HasDerivAt ξ (deriv ξ q) q)
    (hξ' : HasDerivAt (deriv ξ) ξ₂ q) :
    HasDerivAt (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u))
      ((1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) * ξ₂ * (-M + q)) q := by
  let C : ℝ := parisiQConst ξ ms qs r
  let c : ℝ := (1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val)
  have hθ := hasDerivAt_parisiTheta hξ hξ'
  have hbase := hX₀.add (hθ.const_mul c)
  have hall := (hasDerivAt_const q C).add hbase
  have hfun :
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u))
        = (fun u => C +
          (randomFieldParisiX₀ μh ξ ms (qUpdate qs r u) + c * parisiTheta ξ u)) := by
    funext u
    rw [randomFieldParisiFunctional_qUpdate_eq]
  rw [hfun]
  refine hall.congr_deriv ?_
  dsimp [c]
  ring

/-- The random-field form of (14.220) obtained from the concrete Parisi recursion and
differentiation under the external-field integral. -/
theorem hasDerivAt_randomFieldParisiFunctional_qUpdate_concrete
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs)
    (hleftq : qExt qs r.val < qs r)
    (hrightq : qs r < qExt qs (r.val + 2)) :
    HasDerivAt (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u))
      ((1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) *
        deriv (deriv ξ) (qs r) *
          (-randomFieldParisiQMoment μh ξ ms qs r + qs r)) (qs r) := by
  apply hasDerivAt_randomFieldParisiFunctional_qUpdate ms qs r
    (hasDerivAt_randomFieldParisiX₀_qUpdate_concrete ms qs r hμh hm hξ hq
      hleftq hrightq)
    (hξ.hasDeriv (qs r) (hq.mem_Icc r))
    (hξ.hasDeriv_deriv (qs r) (hq.mem_Icc r))

/-- At an interior local minimum of the random-field functional, (14.220) gives the averaged
stationarity equation. -/
theorem randomFieldParisiQ_eq_moment_of_isLocalMin
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) {q ξ₂ M : ℝ}
    (hmin : IsLocalMin
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u)) q)
    (hX₀ : HasDerivAt
      (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
      ((-1 / 2 : ℝ) * ξ₂ * (mExt ms (r.val + 1) - mExt ms r.val) * M) q)
    (hξ : HasDerivAt ξ (deriv ξ q) q)
    (hξ' : HasDerivAt (deriv ξ) ξ₂ q)
    (hm : mExt ms (r.val + 1) ≠ mExt ms r.val) (hξ₂ : ξ₂ ≠ 0) : q = M := by
  have hd := hasDerivAt_randomFieldParisiFunctional_qUpdate ms qs r hX₀ hξ hξ'
  have hz := hmin.hasDerivAt_eq_zero hd
  have hc : (1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) * ξ₂ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) hξ₂
    exact sub_ne_zero.mpr hm
  have hz' :
      ((1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) * ξ₂) * (-M + q) = 0 := by
    simpa [mul_assoc] using hz
  have hlast : -M + q = 0 := (mul_eq_zero.mp hz').resolve_left hc
  linarith

/-- The averaged stationarity equation with the mass gap supplied by admissibility. -/
theorem randomFieldParisiQ_eq_moment_of_isLocalMin_of_admissible
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) {q ξ₂ M : ℝ}
    (hm : ParisiMAdmissible ms) (hξ₂ : 0 < ξ₂)
    (hmin : IsLocalMin
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u)) q)
    (hX₀ : HasDerivAt
      (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
      ((-1 / 2 : ℝ) * ξ₂ * (mExt ms (r.val + 1) - mExt ms r.val) * M) q)
    (hξ : HasDerivAt ξ (deriv ξ q) q)
    (hξ' : HasDerivAt (deriv ξ) ξ₂ q) : q = M := by
  apply randomFieldParisiQ_eq_moment_of_isLocalMin ms qs r hmin hX₀ hξ hξ'
  · exact ne_of_gt (hm.mExt_gap_pos r) |>.imp fun heq => sub_eq_zero.mpr heq
  · exact ne_of_gt hξ₂

/-- Conditional reduction of Proposition 14.7.5 for a common i.i.d. external-field law.
Here `M r` includes the outer expectation over that law; its derivative and endpoint bounds
remain hypotheses. -/
theorem randomFieldParisiQ_strict_chain_and_eq_moment_of_isMin_of_derivatives
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (M ξ₂ : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    (hX₀ : ∀ r, HasDerivAt
      (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
      ((-1 / 2 : ℝ) * ξ₂ r * (mExt ms (r.val + 1) - mExt ms r.val) * M r) (qs r))
    (hξ : ∀ r, HasDerivAt ξ (deriv ξ (qs r)) (qs r))
    (hξ' : ∀ r, HasDerivAt (deriv ξ) (ξ₂ r) (qs r))
    (hξ₂ : ∀ r, 0 < ξ₂ r) (hMfirst : 0 < M 0) (hMlast : M (Fin.last k) < 1) :
    (∀ r : ℕ, r ≤ k + 1 → qExt qs r < qExt qs (r + 1)) ∧
      ∀ r, qs r = M r := by
  have hd (r : Fin (k + 1)) :=
    hasDerivAt_randomFieldParisiFunctional_qUpdate ms qs r (hX₀ r) (hξ r) (hξ' r)
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
  exact randomFieldParisiQ_eq_moment_of_isLocalMin_of_admissible ms qs r hm (hξ₂ r)
    (hmin.isLocalMin_qUpdate ms qs hq0 hq1 r) (hX₀ r) (hξ r) (hξ' r)

/-- Proposition 14.7.5 after its endpoint inequalities are established.  The derivatives and
moments in the stationarity equations come from the concrete recursion and the external-field
integral. -/
theorem randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin_of_endpoints
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) :
    (∀ n : ℕ, n ≤ k + 1 → qExt qs n < qExt qs (n + 1)) ∧
      ∀ r, qs r = randomFieldParisiQMoment μh ξ ms qs r := by
  have hchain : ∀ n : ℕ, n ≤ k + 1 → qExt qs n < qExt qs (n + 1) :=
    fun n hn => qExt_strict_succ hmin.1.1 hq0 hq1 hn
  refine ⟨hchain, ?_⟩
  intro r
  have hqmem : qs r ∈ Icc (0 : ℝ) 1 := hmin.1.mem_Icc r
  have hqpos : 0 < qs r := hq0.trans_le (hmin.1.monotone (Fin.zero_le r))
  have hξ₂pos : 0 < deriv (deriv ξ) (qs r) :=
    hξ.second_pos _ hqmem (ne_of_gt hqpos)
  have hleftq : qExt qs r.val < qs r := by
    simpa [qExt_succ_of_lt qs r.isLt] using hchain r.val (by omega)
  have hrightq : qs r < qExt qs (r.val + 2) := by
    simpa [qExt_succ_of_lt qs r.isLt] using hchain (r.val + 1) (by omega)
  have hd := hasDerivAt_randomFieldParisiX₀_qUpdate_concrete ms qs r hμh hm hξ
    hmin.1 hleftq hrightq
  exact randomFieldParisiQ_eq_moment_of_isLocalMin_of_admissible ms qs r hm hξ₂pos
    (hmin.isLocalMin_qUpdate ms qs hq0 hq1 r) hd
    (hξ.hasDeriv _ hqmem) (hξ.hasDeriv_deriv _ hqmem)

/-- A nondegenerate external-field law rules out a collapsed first overlap by an admissible
right-hand variation.  No positivity assumption on `ξ''(0)` is used: positivity away from zero
and continuity of the concrete first moment give a short interval on which the functional is
strictly decreasing. -/
theorem randomFieldParisiQ_first_pos_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    0 < qs 0 := by
  by_contra hn
  have hqzero : qs 0 = 0 := le_antisymm (not_lt.mp hn) hmin.1.2.1
  let M : ℝ → ℝ := fun u =>
    randomFieldParisiQMoment μh ξ ms (qUpdate qs 0 u) 0
  let F : ℝ → ℝ := fun u =>
    randomFieldParisiFunctional μh ξ ms (qUpdate qs 0 u)
  have hM0 : 0 < M 0 := by
    have hsame : qUpdate qs 0 0 = qs := by
      funext p
      by_cases hp : p = 0
      · subst p
        simp [qUpdate, hqzero]
      · simp [qUpdate, hp]
    change 0 < randomFieldParisiQMoment μh ξ ms (qUpdate qs 0 0) 0
    rw [hsame]
    exact randomFieldParisiQMoment_first_pos qs hm hqzero hμ
  have hMc : ContinuousAt M 0 := by
    exact continuousAt_randomFieldParisiQMoment_first_qUpdate_zero qs hm hξ
  have hMev : ∀ᶠ u in nhds 0, M 0 / 2 < M u :=
    hMc.eventually (Ioi_mem_nhds (half_lt_self hM0))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 hMev
  let qR : ℝ := qExt qs 2
  have hqR : 0 < qR := by
    by_cases hk : k = 0
    · subst k
      dsimp [qR]
      rw [qExt_of_le qs (by omega)]
      norm_num
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      dsimp [qR]
      rw [qExt_succ_of_lt qs (by omega : 1 < k + 1)]
      have h01 : (0 : Fin (k + 1)) < ⟨1, by omega⟩ :=
        Fin.mk_lt_mk.mpr Nat.zero_lt_one
      simpa [hqzero] using hmin.1.1 h01
  let b : ℝ := min (min ε qR) (min (M 0 / 2) 1) / 2
  have hbpos : 0 < b := by
    dsimp [b]
    positivity
  have hbε : b < ε := by
    dsimp [b]
    have hminpos : 0 < min (min ε qR) (min (M 0 / 2) 1) := by positivity
    have hle : min (min ε qR) (min (M 0 / 2) 1) ≤ ε :=
      (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hbqR : b < qR := by
    dsimp [b]
    have hminpos : 0 < min (min ε qR) (min (M 0 / 2) 1) := by positivity
    have hle : min (min ε qR) (min (M 0 / 2) 1) ≤ qR :=
      (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hbM : b < M 0 / 2 := by
    dsimp [b]
    have hminpos : 0 < min (min ε qR) (min (M 0 / 2) 1) := by positivity
    have hle : min (min ε qR) (min (M 0 / 2) 1) ≤ M 0 / 2 :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hb1 : b < 1 := by
    dsimp [b]
    have hminpos : 0 < min (min ε qR) (min (M 0 / 2) 1) := by positivity
    have hle : min (min ε qR) (min (M 0 / 2) 1) ≤ 1 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hMlarge : ∀ u ∈ Icc (0 : ℝ) b, M 0 / 2 < M u := by
    intro u hu
    apply hεsub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hu.1]
    exact hu.2.trans_lt hbε
  have hadm : ∀ u ∈ Ioc (0 : ℝ) b,
      ParisiQAdmissible (qUpdate qs 0 u) := by
    intro u hu
    apply hmin.1.qUpdate 0 hu.1.le (hu.2.trans_lt hb1).le
    · intro p hp
      exact (not_lt_of_ge (Fin.zero_le p) hp).elim
    · intro p hp
      by_cases hk : k = 0
      · subst k
        have hp0 : p = 0 := Fin.eq_zero p
        subst p
        exact (lt_irrefl 0 hp).elim
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have hfirst : (⟨1, by omega⟩ : Fin (k + 1)) ≤ p := by
          exact Fin.mk_le_mk.mpr (Nat.one_le_iff_ne_zero.2 (by
            intro hp0
            apply ne_of_gt hp
            exact Fin.ext hp0))
        have hqRle : qR ≤ qs p := by
          dsimp [qR]
          rw [qExt_succ_of_lt qs (by omega : 1 < k + 1)]
          exact hmin.1.monotone hfirst
        exact hu.2.trans_lt hbqR |>.trans_le hqRle
  have hderiv : ∀ u ∈ Ioc (0 : ℝ) b, HasDerivAt F
      ((1 / 2 : ℝ) * (mExt ms 1 - mExt ms 0) * deriv (deriv ξ) u * (-M u + u)) u := by
    intro u hu
    let qu := qUpdate qs 0 u
    have hqu : ParisiQAdmissible qu := hadm u hu
    have humem : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, (hu.2.trans_lt hb1).le⟩
    have hleft : qExt qu 0 < qu 0 := by simp [qu, qUpdate, hu.1]
    have hright : qu 0 < qExt qu 2 := by
      dsimp [qu]
      rw [qUpdate_self, qExt_qUpdate_of_gt qs 0 u (by norm_num)]
      exact hu.2.trans_lt hbqR
    have hd := hasDerivAt_randomFieldParisiFunctional_qUpdate_concrete
      ms qu 0 hμh hm hξ hqu hleft hright
    simpa [F, M, qu, qUpdate, mExt_zero] using hd
  have hderivneg : ∀ u ∈ interior (Icc (0 : ℝ) b), deriv F u < 0 := by
    intro u hu
    rw [interior_Icc] at hu
    have huioc : u ∈ Ioc (0 : ℝ) b := ⟨hu.1, hu.2.le⟩
    have hd := hderiv u huioc
    rw [hd.deriv]
    have hgap : 0 < mExt ms 1 - mExt ms 0 := hm.mExt_gap_pos 0
    have hsecond : 0 < deriv (deriv ξ) u :=
      hξ.second_pos u ⟨hu.1.le, (hu.2.trans hb1).le⟩ (ne_of_gt hu.1)
    have huM : u < M u :=
      (hu.2.trans hbM).trans (hMlarge u ⟨hu.1.le, hu.2.le⟩)
    have hcoef : 0 < (1 / 2 : ℝ) * (mExt ms 1 - mExt ms 0) *
        deriv (deriv ξ) u := mul_pos (mul_pos (by norm_num) hgap) hsecond
    simpa [sub_eq_add_neg, add_comm] using
      mul_neg_of_pos_of_neg hcoef (sub_neg.mpr huM)
  have hFcont : ContinuousOn F (Icc (0 : ℝ) b) := by
    intro u hu
    by_cases hu0 : u = 0
    · subst u
      have hc := (continuousWithinAt_randomFieldParisiFunctional_qUpdate
        ms qs 0 hμh hm hξ hmin.1).mono (Icc_subset_Icc_right hb1.le)
      simpa [F, hqzero] using hc
    · have huioc : u ∈ Ioc (0 : ℝ) b := ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), hu.2⟩
      exact (hderiv u huioc).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn F (Icc (0 : ℝ) b) :=
    strictAntiOn_of_deriv_neg (convex_Icc 0 b) hFcont hderivneg
  have hFbF0 : F b < F 0 := hanti ⟨le_rfl, hbpos.le⟩ ⟨hbpos.le, le_rfl⟩ hbpos
  have hminle : F 0 ≤ F b := by
    have hsame : qUpdate qs 0 0 = qs := by
      funext p
      by_cases hp : p = 0
      · subst p
        simp [qUpdate, hqzero]
      · simp [qUpdate, hp]
    change randomFieldParisiFunctional μh ξ ms (qUpdate qs 0 0) ≤
      randomFieldParisiFunctional μh ξ ms (qUpdate qs 0 b)
    rw [hsame]
    exact hmin.le_qUpdate 0 hbpos.le hb1.le
      (fun p hp => (not_lt_of_ge (Fin.zero_le p) hp).elim)
      (fun p hp => by
        have hbmem : b ∈ Ioc (0 : ℝ) b := ⟨hbpos, le_rfl⟩
        have hp' := (hadm b hbmem).1 hp
        have hpne : p ≠ 0 := ne_of_gt hp
        simpa [qUpdate, hpne] using hp')
  linarith

/-- The endpoint derivative is averaged using a common bound independent of the site field.
Only admissible left-hand values are used. -/
theorem hasDerivWithinAt_randomFieldParisiX₀_last_qUpdate
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs)
    (hqlast : qs (Fin.last k) = 1) :
    HasDerivWithinAt
      (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs (Fin.last k) u))
      ((-1 / 2 : ℝ) * deriv (deriv ξ) 1 * (1 - mExt ms k) *
        randomFieldParisiQMoment μh ξ ms qs (Fin.last k)) (Iic 1) 1 := by
  let r : Fin (k + 1) := Fin.last k
  let qL := qExt qs r.val
  let gap := mExt ms (r.val + 1) - mExt ms r.val
  let f : ℝ → ℝ → ℝ := fun u h =>
    parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h)
  let D : ℝ → ℝ → ℝ := fun u h =>
    (-1 / 2 : ℝ) * deriv (deriv ξ) u * gap *
      parisiQMoment ξ h ms (qUpdate qs r u) r
  let d : ℝ → ℝ := fun h =>
    (-1 / 2 : ℝ) * deriv (deriv ξ) 1 * gap * parisiQMoment ξ h ms qs r
  let K := (1 / 2 : ℝ) * gap * deriv (deriv ξ) 1
  have hgap : 0 < gap := hm.mExt_gap_pos r
  have hgapEq : gap = 1 - mExt ms k := by simp [gap, r, mExt]
  have hqLlt : qL < 1 := by
    by_cases hk : k = 0
    · subst k
      simp [qL, r, qExt_zero]
    · change qExt qs k < 1
      have hprev : (⟨k - 1, by omega⟩ : Fin (k + 1)) < Fin.last k :=
        Fin.mk_lt_mk.mpr (by simp [Fin.last]; omega)
      rw [qExt, if_neg hk, dif_pos (by omega : k - 1 < k + 1)]
      simpa [hqlast] using hq.1 hprev
  have hqLmem : qL ∈ Icc (0 : ℝ) 1 :=
    qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _
  have hsame : qUpdate qs r 1 = qs := by
    funext p
    by_cases hp : p = r
    · subst p
      simp [qUpdate, r, hqlast]
    · simp [qUpdate, hp]
  have hfm : ∀ u, Measurable (f u) := fun u =>
    measurable_parisiX₀_logCosh ξ ms (qUpdate qs r u) hm.2.1
      (fun p => (hm.2.2 p).le)
  have hfi : Integrable (f 1) μh := by
    dsimp [f]
    rw [hsame]
    exact integrable_parisiX₀_logCosh hμh ξ ms qs hm.2.1 (fun p => (hm.2.2 p).le)
  have hdm : Measurable d :=
    (measurable_parisiQMoment_externalField qs r hm).const_mul _
  have hbound (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) 1) (h : ℝ)
      (Q : Fin (k + 1) → ℝ) :
      ‖(-1 / 2 : ℝ) * deriv (deriv ξ) u * gap * parisiQMoment ξ h ms Q r‖ ≤ K := by
    have hspos := hξ.second_pos u ⟨hu.1.le, hu.2⟩ (ne_of_gt hu.1)
    have hsle := hξ.monotoneOn_second hu ⟨zero_lt_one, le_rfl⟩ hu.2
    have hM := abs_parisiQMoment_le_one (ξ := ξ) (h := h) Q r hm
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      show |(-1 / 2 : ℝ)| = 1 / 2 by norm_num,
      abs_of_nonneg hspos.le, abs_of_nonneg hgap.le]
    calc
      _ ≤ 1 / 2 * deriv (deriv ξ) u * gap * 1 := by gcongr
      _ ≤ 1 / 2 * deriv (deriv ξ) 1 * gap * 1 := by gcongr
      _ = K := by dsimp [K]; ring
  have hDb : ∀ h, ∀ u ∈ Ioo qL 1, ‖D u h‖ ≤ K := by
    intro h u hu
    exact hbound u ⟨hqLmem.1.trans_lt hu.1, hu.2.le⟩ h (qUpdate qs r u)
  have hdb : ∀ h, ‖d h‖ ≤ K := fun h => hbound 1 ⟨zero_lt_one, le_rfl⟩ h qs
  have hD : ∀ h, ∀ u ∈ Ioo qL 1,
      HasDerivAt (fun v => f v h) (D u h) u := by
    intro h u hu
    let qu := qUpdate qs r u
    have humem : u ∈ Icc (0 : ℝ) 1 := ⟨hqLmem.1.trans hu.1.le, hu.2.le⟩
    have hquself : qu r = u := qUpdate_self qs r u
    have hquleft : qExt qu r.val = qL := qExt_qUpdate_of_lt qs r u (by omega)
    have hquright : qExt qu (r.val + 2) = 1 := by
      rw [qExt_qUpdate_of_gt qs r u (by omega)]
      exact qExt_of_le qs (by simp [r])
    have hleft : deriv ξ (qExt qu r.val) < deriv ξ (qu r) := by
      rw [hquleft, hquself]
      exact hξ.strictMonoOn_deriv hqLmem humem hu.1
    have hright : deriv ξ (qu r) < deriv ξ (qExt qu (r.val + 2)) := by
      rw [hquself, hquright]
      exact hξ.strictMonoOn_deriv humem ⟨zero_le_one, le_rfl⟩ hu.2
    have hξd := hξ.hasDeriv_deriv u humem
    rw [← hquself] at hξd
    have hd := hasDerivAt_parisiX₀_qUpdate (ξ := ξ) (h := h) qu r hm hξd hleft hright
    have heq : (fun v => parisiX₀ ξ ms (qUpdate qu r v) (parisiLogCoshTerminal h)) =
        fun v => f v h := by
      funext v
      congr 1
      funext p
      simp [f, qu, qUpdate]
    rw [heq] at hd
    simpa [D, gap, qu, hquself] using hd
  have hd : ∀ h, HasDerivWithinAt (fun u => f u h) (d h) (Iic 1) 1 := by
    intro h
    simpa [f, d, r, hgapEq] using
      hasDerivWithinAt_parisiX₀_last_qUpdate (h := h) qs hm hξ hq hqlast
  have havg := hasDerivWithinAt_integral_of_dominated_left hqLlt hfm hfi hdm
    (integrable_const K : Integrable (fun _ : ℝ => K) μh) hDb hdb hD hd
  have hdEq : (∫ h, d h ∂μh) = (-1 / 2 : ℝ) * deriv (deriv ξ) 1 *
      (1 - mExt ms k) * randomFieldParisiQMoment μh ξ ms qs (Fin.last k) := by
    simp only [d, integral_const_mul, hgapEq, r, randomFieldParisiQMoment]
  rw [hdEq] at havg
  exact havg

/-- The admissible left derivative of the actual law-level functional at the last endpoint. -/
theorem hasDerivWithinAt_randomFieldParisiFunctional_last_qUpdate
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs)
    (hqlast : qs (Fin.last k) = 1) :
    HasDerivWithinAt
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs (Fin.last k) u))
      ((1 / 2 : ℝ) * (1 - mExt ms k) * deriv (deriv ξ) 1 *
        (1 - randomFieldParisiQMoment μh ξ ms qs (Fin.last k))) (Iic 1) 1 := by
  let r : Fin (k + 1) := Fin.last k
  let c := (1 / 2 : ℝ) * (1 - mExt ms k)
  have hX := hasDerivWithinAt_randomFieldParisiX₀_last_qUpdate ms qs hμh hm hξ hq hqlast
  have hθ := hasDerivAt_parisiTheta (hξ.hasDeriv 1 ⟨zero_le_one, le_rfl⟩)
    (hξ.hasDeriv_deriv 1 ⟨zero_le_one, le_rfl⟩)
  have hall := (hX.add (hθ.const_mul c).hasDerivWithinAt).const_add
    (parisiQConst ξ ms qs r)
  have heq : (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u)) =
      fun u => parisiQConst ξ ms qs r +
        (randomFieldParisiX₀ μh ξ ms (qUpdate qs r u) + c * parisiTheta ξ u) := by
    funext u
    simpa [r, c, mExt] using randomFieldParisiFunctional_qUpdate_eq μh ξ ms qs r u
  rw [heq]
  exact hall.congr_deriv (by dsimp [c]; ring)

/-- The last overlap cannot equal one: its admissible left derivative is strictly positive. -/
theorem randomFieldParisiQ_last_lt_one_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    qs (Fin.last k) < 1 := by
  by_contra hn
  have ho : qs (Fin.last k) = 1 := le_antisymm hmin.1.2.2 (not_lt.mp hn)
  have hd := hasDerivWithinAt_randomFieldParisiFunctional_last_qUpdate
    ms qs hμh hm hξ hmin.1 ho
  have hnonpos := hmin.last_derivWithin_nonpos ho (by simpa [ho] using hd)
  have hM := randomFieldParisiQMoment_last_lt_one (μh := μh) (ξ := ξ) qs hm ho
  have hgap : 0 < 1 - mExt ms k := by
    simpa [mExt] using hm.mExt_gap_pos (Fin.last k)
  have hs : 0 < deriv (deriv ξ) 1 :=
    hξ.second_pos 1 ⟨zero_le_one, le_rfl⟩ (by norm_num)
  have hpos : 0 < (1 / 2 : ℝ) * (1 - mExt ms k) * deriv (deriv ξ) 1 *
      (1 - randomFieldParisiQMoment μh ξ ms qs (Fin.last k)) := by positivity
  linarith

/-- A finite second moment under a probability law supplies the first-moment integrability
needed for the Parisi functional. -/
lemma NondegenerateExternalFieldLaw.integrable_id
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh) :
    Integrable id μh := by
  apply ((integrable_const (1 : ℝ)).add hμ.sq_integrable).mono'
    measurable_id.aestronglyMeasurable
  filter_upwards [] with h
  change ‖h‖ ≤ 1 + h ^ 2
  rw [Real.norm_eq_abs]
  rcases le_total 0 h with hh | hh
  · rw [abs_of_nonneg hh]
    nlinarith [sq_nonneg (h - 1)]
  · rw [abs_of_nonpos hh]
    nlinarith [sq_nonneg (h + 1)]

/-- Proposition 14.7.5 for a nondegenerate probability law of i.i.d. external fields.
All derivatives and endpoint bounds are consequences of the actual recursion. -/
theorem randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    (∀ n : ℕ, n ≤ k + 1 → qExt qs n < qExt qs (n + 1)) ∧
      ∀ r, qs r = randomFieldParisiQMoment μh ξ ms qs r := by
  exact randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin_of_endpoints
    ms qs hμ.integrable_id hm hξ hmin
    (randomFieldParisiQ_first_pos_of_isMin ms qs hμ.integrable_id hm hξ hμ hmin)
    (randomFieldParisiQ_last_lt_one_of_isMin ms qs hμ.integrable_id hm hξ hmin)

/-- A constant site law recovers the deterministic concrete moment, also at zero field. -/
@[simp] theorem randomFieldParisiQMoment_dirac (h : ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) :
    randomFieldParisiQMoment (Measure.dirac h) ξ ms qs r = parisiQMoment ξ h ms qs r := by
  simp [randomFieldParisiQMoment]

/-- A constant external field is nondegenerate exactly when it is nonzero. -/
@[simp] theorem nondegenerateExternalFieldLaw_dirac_iff (h : ℝ) :
    NondegenerateExternalFieldLaw (Measure.dirac h) ↔ h ≠ 0 := by
  constructor
  · intro hμ
    have hp := hμ.second_moment_pos
    simpa using (ne_of_gt (show 0 < h ^ 2 by simpa using hp)).imp
      (fun hz => by simp [hz])
  · intro hh
    refine ⟨?_, ?_⟩
    · exact integrable_dirac (by simp)
    · simpa using sq_pos_of_ne_zero hh

/-- The stationarity moment in Proposition 14.7.5 is explicitly the expectation at any
coordinate of the i.i.d. product law. -/
theorem iidExternalFieldParisiQ_strict_chain_and_eq_moment_of_isMin
    {N : ℕ} (i : Fin N) {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    (∀ n : ℕ, n ≤ k + 1 → qExt qs n < qExt qs (n + 1)) ∧
      ∀ r, qs r = ∫ hVec, parisiQMoment ξ (hVec i) ms qs r
        ∂externalFieldVecLaw N μh := by
  obtain ⟨hchain, hmoment⟩ :=
    randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin ms qs hm hξ hμ hmin
  refine ⟨hchain, fun r => ?_⟩
  rw [hmoment r]
  exact randomFieldParisiQMoment_eq_integral_externalFieldVec_apply i ξ ms qs r hm

end

end SpinGlass
