import SpinGlass.ParisiFunctional
import Common.Mathlib.Analysis.SpecialFunctions.Tanh
import Common.Mathlib.Probability.PointProcess.CascadeColeHopf
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# ColeHopf

Generic Cole-Hopf spatial derivatives and variance splitting.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

/-! ### Spatial derivatives of a Cole-Hopf iterate -/

/-- The recursively propagated first spatial derivative of a Cole-Hopf iterate. -/
def coleHopfIterateDeriv : (j : ℕ) → (Fin j → ℝ) → (Fin j → ℝ≥0)
    → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | 0, _, _, _, G' => G'
  | j + 1, ms, vs, G, G' => fun x =>
      ∫ z, coleHopfIterateDeriv j (Fin.tail ms) (Fin.tail vs) G G' (x + z)
          * coleHopfQ (ms 0) (vs 0)
              (coleHopfIterate j (Fin.tail ms) (Fin.tail vs) G) x z
        ∂gaussianReal 0 (vs 0)

/-- The recursively propagated second spatial derivative of a Cole-Hopf iterate. -/
def coleHopfIterateDeriv2 : (j : ℕ) → (Fin j → ℝ) → (Fin j → ℝ≥0)
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
            · exact hA''b x
            · exact hA'b x
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
            · exact hIb x
            · exact hB'b x
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
    · simp only [Fin.append_right]
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
def coleHopfSplitMoment (m m' : ℝ) (vR vL : ℝ≥0)
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
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, NNReal.coe_sub hle]
      change dist (v a : ℝ) (v₀ : ℝ) < δ at ha
      simpa only [Real.dist_eq] using ha
    have hm := hball hdiff
    change coleHopfModulus m L (Real.toNNReal ((v a - v₀ : ℝ≥0) : ℝ)) < ε at hm
    rw [Real.toNNReal_coe] at hm
    exact (abs_coleHopf_sub_coleHopf_le hAm hAlip m hle x).trans_lt hm
  · rw [abs_sub_comm]
    have hdiff : (((v₀ - v a : ℝ≥0) : ℝ)) ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, NNReal.coe_sub hle]
      change dist (v a : ℝ) (v₀ : ℝ) < δ at ha
      simpa only [Real.dist_eq, abs_sub_comm] using ha
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
    measurable_fst.add (Finset.measurable_sum _ fun p _ =>
      (measurable_pi_apply p).comp measurable_snd)
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


end

end SpinGlass
