import SpinGlass.Parisi.Minimizer.QVariation.Parameters
import SpinGlass.Parisi.Guerra.LogCosh

/-!
# Terminal

Log-cosh terminal data and strict derivative properties.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

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

/-- Positive-mass log-cosh iterates have bounded first and second spatial derivatives. -/
theorem coleHopfIterate_logCosh_regular {j : ℕ} (ms : Fin j → ℝ)
    (vs : Fin j → ℝ≥0) (h : ℝ) (hpos : ∀ i, 0 < ms i) :
    (∀ x, HasDerivAt (coleHopfIterate j ms vs (parisiLogCoshTerminal h))
      (coleHopfIterateDeriv j ms vs (parisiLogCoshTerminal h)
        (parisiLogCoshTerminalDeriv h) x) x) ∧
    ∃ C : ℝ,
      (∀ x, HasDerivAt (coleHopfIterateDeriv j ms vs (parisiLogCoshTerminal h)
          (parisiLogCoshTerminalDeriv h))
        (coleHopfIterateDeriv2 j ms vs (parisiLogCoshTerminal h)
          (parisiLogCoshTerminalDeriv h) (parisiLogCoshTerminalDeriv2 h) x) x) ∧
      Continuous (coleHopfIterateDeriv2 j ms vs (parisiLogCoshTerminal h)
        (parisiLogCoshTerminalDeriv h) (parisiLogCoshTerminalDeriv2 h)) ∧
      (∀ x, |coleHopfIterateDeriv j ms vs (parisiLogCoshTerminal h)
        (parisiLogCoshTerminalDeriv h) x| ≤ 1) ∧
      ∀ x, |coleHopfIterateDeriv2 j ms vs (parisiLogCoshTerminal h)
        (parisiLogCoshTerminalDeriv h) (parisiLogCoshTerminalDeriv2 h) x| ≤ C :=
  coleHopfIterate_deriv_regular ms vs
    (hasDerivAt_parisiLogCoshTerminal h) (hasDerivAt_parisiLogCoshTerminalDeriv h)
    (continuous_parisiLogCoshTerminalDeriv2 h)
    (fun x => (abs_parisiLogCoshTerminalDeriv_lt_one h x).le)
    (abs_parisiLogCoshTerminalDeriv2_le_one h) hpos

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
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (_hpos : ∀ i, 0 < ms i) (h : ℝ) :
    coleHopfIterateDeriv j ms vs (parisiLogCoshTerminal h)
        (parisiLogCoshTerminalDeriv h) 0 =
      coleHopfIterateDeriv j ms vs (parisiLogCoshTerminal 0)
        (parisiLogCoshTerminalDeriv 0) h := by
  have hG : parisiLogCoshTerminal h = fun y => parisiLogCoshTerminal 0 (h + y) := by
    funext y
    simp only [parisiLogCoshTerminal, zero_add]
  have hG' : parisiLogCoshTerminalDeriv h =
      fun y => parisiLogCoshTerminalDeriv 0 (h + y) := by
    funext y
    simp only [parisiLogCoshTerminalDeriv, zero_add]
  rw [hG, hG']
  simpa only [add_zero] using
    coleHopfIterateDeriv_translate ms vs (parisiLogCoshTerminal 0)
      (parisiLogCoshTerminalDeriv 0) h 0

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
    coleHopfIterate_logCosh_regular ms vs 0 hpos
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
      simpa only [Function.comp_def, neg_zero, mul_neg_one] using
        (hB (-0)).comp 0 (hasDerivAt_id (0 : ℝ)).neg
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
  rw [coleHopfIterateDeriv_parisiLogCoshTerminal_translate ms vs hpos h]
  exact hB'h

end

end SpinGlass
