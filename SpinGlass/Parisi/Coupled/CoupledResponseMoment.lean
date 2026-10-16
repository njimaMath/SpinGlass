import SpinGlass.Parisi.Coupled.Derivative.Zero
import SpinGlass.Parisi.Variational.ParisiCascadeTransport
import SpinGlass.Parisi.Minimizer.QVariation.Terminal
import SpinGlass.Parisi.Variational.ParisiOuterEndpoints
import SpinGlass.Parisi.Variational.ParisiSpatialThird

/-!
# The coupled conditional square as a concrete response moment

The nonnegative encoding of the zero-coupling slope in (14.315) is
identified with the actual Cole-Hopf suffix gradient under the normalized
prefix cascade law. Gaussian variances may vanish.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

private theorem logCosh_lipschitz :
    ∀ x y, |parisiLogCoshTerminal 0 y - parisiLogCoshTerminal 0 x| ≤ 1 * |y - x| := by
  simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0

/-- The full normalized cascade transports tanh to the actual first spatial
derivative of its log-cosh Cole-Hopf iterate, as in (14.215). -/
theorem coleHopfIterate_logCosh_deriv_eq_tilt {n : ℕ}
    (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1) (x : ℝ) :
    deriv (coleHopfIterate n ms vs (parisiLogCoshTerminal 0)) x =
      ∫ zs, Real.tanh (x + ∑ p, zs p)
        ∂cascadeTiltMeasure n ms (fun p => gaussianReal 0 (vs p))
          (fun zs => ENNReal.ofReal (Real.exp
            (parisiLogCoshTerminal 0 (x + ∑ p, zs p)))) := by
  have ht : Continuous Real.tanh :=
    continuous_iff_continuousAt.2 fun y => (Real.hasDerivAt_tanh y).continuousAt
  have hd := hasDerivAt_coleHopfIterate ms vs hpos hle
    (G := fun l y => parisiLogCoshTerminal 0 (l + y))
    (G' := fun l y => Real.tanh (l + y)) (L := 1) (C := 1)
    (fun l => ht.measurable.comp (measurable_const.add measurable_id))
    (fun l y => by
      simpa only [parisiLogCoshTerminalDeriv, zero_add, Function.comp_def, id_eq, mul_one] using
        (hasDerivAt_parisiLogCoshTerminal 0 (l + y)).comp l
          ((hasDerivAt_id l).add_const y))
    (fun l y => (Real.abs_tanh_lt_one (l + y)).le)
    (fun l y z => by
      simpa only [add_sub_add_left_eq_sub] using logCosh_lipschitz (l + y) (l + z)) x 0
  have he : (fun l => coleHopfIterate n ms vs
      (fun y => parisiLogCoshTerminal 0 (l + y)) 0) =
      coleHopfIterate n ms vs (parisiLogCoshTerminal 0) := by
    funext l
    rw [coleHopfIterate_translate, add_zero]
  rw [he] at hd
  simpa only [zero_add] using hd.deriv

theorem cascadeTilt_shiftedTanh_eq {n : ℕ}
    (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    (x c : ℝ) (hc : 1 ≤ c) :
    cascadeTilt n ms (fun p => gaussianReal 0 (vs p))
      (fun zs => ENNReal.ofReal (Real.exp
        (parisiLogCoshTerminal 0 (x + ∑ p, zs p))))
      (fun zs => ENNReal.ofReal (Real.tanh (x + ∑ p, zs p) + c)) =
      ENNReal.ofReal (deriv (coleHopfIterate n ms vs (parisiLogCoshTerminal 0)) x + c) := by
  let μ := cascadeTiltMeasure n ms (fun p => gaussianReal 0 (vs p))
    (fun zs => ENNReal.ofReal (Real.exp (parisiLogCoshTerminal 0 (x + ∑ p, zs p))))
  have hAm := measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0)
  have : IsProbabilityMeasure μ :=
    isProbabilityMeasure_cascadeTiltMeasure_comp_add_sum ms vs hpos hle hAm
      logCosh_lipschitz x
  have ht : Continuous Real.tanh :=
    continuous_iff_continuousAt.2 fun y => (Real.hasDerivAt_tanh y).continuousAt
  have hsum : Measurable (fun zs : Fin n → ℝ => x + ∑ p, zs p) :=
    measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)
  have hi : Integrable (fun zs : Fin n → ℝ => Real.tanh (x + ∑ p, zs p)) μ :=
    Integrable.of_bound (ht.measurable.comp hsum).aestronglyMeasurable 1
      (.of_forall fun zs => by
        rw [Real.norm_eq_abs]
        exact (Real.abs_tanh_lt_one _).le)
  have hG : Measurable (fun zs : Fin n → ℝ => ENNReal.ofReal (Real.exp
      (parisiLogCoshTerminal 0 (x + ∑ p, zs p)))) := (hAm.comp hsum).exp.ennreal_ofReal
  have hF : Measurable (fun zs : Fin n → ℝ =>
      ENNReal.ofReal (Real.tanh (x + ∑ p, zs p) + c)) :=
    ((ht.measurable.comp hsum).add measurable_const).ennreal_ofReal
  calc
    _ = ∫⁻ zs, ENNReal.ofReal (Real.tanh (x + ∑ p, zs p) + c) ∂μ :=
      (lintegral_cascadeTiltMeasure n ms _ hG hF).symm
    _ = ENNReal.ofReal (∫ zs, Real.tanh (x + ∑ p, zs p) + c ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal (hi.add (integrable_const c))
        (.of_forall fun zs => by
          change 0 ≤ Real.tanh (x + ∑ p, zs p) + c
          linarith [Real.neg_one_lt_tanh (x + ∑ p, zs p)])).symm
    _ = _ := by
      rw [integral_add hi (integrable_const c)]
      simp only [integral_const, probReal_univ, one_smul]
      rw [← coleHopfIterate_logCosh_deriv_eq_tilt ms vs hpos hle x]

/-- Split the actual iterate into two prescribed finite lengths. -/
theorem coleHopfIterate_split_at_of_eq {n : ℕ} (r s : ℕ) (hn : n = r + s)
    (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0) (A : ℝ → ℝ) :
    coleHopfIterate n ms vs A =
      coleHopfIterate r (fun p => ms ⟨p.val, by omega⟩)
        (fun p => vs ⟨p.val, by omega⟩)
        (coleHopfIterate s (fun p => ms ⟨r + p.val, by omega⟩)
          (fun p => vs ⟨r + p.val, by omega⟩) A) := by
  subst n
  have hslice {α : Type} (a : Fin (r + s) → α) :
      Fin.append (fun p : Fin r => a ⟨p.val, by omega⟩)
        (fun p : Fin s => a ⟨r + p.val, by omega⟩) = a := by
    funext p
    refine Fin.addCases (fun q => ?_) (fun q => ?_) p
    · simp only [Fin.append_left]
      rfl
    · simp only [Fin.append_right]
      rfl
  conv_lhs => rw [← hslice ms, ← hslice vs]
  exact coleHopfIterate_append r s _ _ _ _ A

/-- Split the actual iterate at any admissible prefix length. -/
theorem coleHopfIterate_split_at_of_le {n : ℕ} (r : ℕ) (hr : r ≤ n)
    (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0) (A : ℝ → ℝ) :
    coleHopfIterate n ms vs A =
      coleHopfIterate r (fun p => ms ⟨p.val, by omega⟩)
        (fun p => vs ⟨p.val, by omega⟩)
        (coleHopfIterate (n - r) (fun p => ms ⟨r + p.val, by omega⟩)
          (fun p => vs ⟨r + p.val, by omega⟩) A) :=
  coleHopfIterate_split_at_of_eq r (n - r) (by omega) ms vs A

/-- Every Gaussian cascade weight is the concrete normalized Cole-Hopf
weight. The identity includes a Gaussian law of variance zero. -/
theorem cascadeW_gaussian_eq_ofReal_coleHopfQ {n : ℕ}
    (ms : Fin (n + 1) → ℝ) (vs : Fin (n + 1) → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) {A : ℝ → ℝ}
    (hA : ∀ x y, |A y - A x| ≤ 1 * |y - x|) (x z : ℝ) :
    cascadeW n ms (fun p => gaussianReal 0 (vs p))
      (fun zs => ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p)))) z =
      ENNReal.ofReal (coleHopfQ (ms 0) (vs 0)
        (coleHopfIterate n (Fin.tail ms) (Fin.tail vs) A) x z) := by
  have hAm := (lipschitzWith_toNNReal_of_abs_sub_le hA).continuous.measurable
  have hcons : (fun ys : Fin n → ℝ =>
      ENNReal.ofReal (Real.exp (A (x + ∑ p, Fin.cons z ys p)))) =
      fun ys => ENNReal.ofReal (Real.exp (A ((x + z) + ∑ p, ys p))) := by
    funext ys
    rw [Fin.sum_cons]
    congr 3
    ring
  rw [cascadeW, hcons]
  change ((cascadeRec n (Fin.tail ms) (fun p => gaussianReal 0 (Fin.tail vs p))
      (fun ys => ENNReal.ofReal (Real.exp (A ((x + z) + ∑ p, ys p))))) /
    cascadeRec (n + 1) ms (fun p => gaussianReal 0 (vs p))
      (fun zs => ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p))))) ^ ms 0 = _
  rw [
    cascadeRec_gaussian_comp_add_sum n (Fin.tail ms) (Fin.tail vs)
      (fun p => hpos p.succ) hAm hA (x + z),
    cascadeRec_gaussian_comp_add_sum (n + 1) ms vs hpos hAm hA x,
    ← ENNReal.ofReal_div_of_pos (Real.exp_pos _),
    ENNReal.ofReal_rpow_of_pos (div_pos (Real.exp_pos _) (Real.exp_pos _)),
    ← Real.exp_sub, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  unfold coleHopfQ
  rw [coleHopfIterate_succ]
  congr 2
  ring

private theorem cascadeTiltSq_shiftedTanh_eq_prefix : ∀ (n r : ℕ) (hr : r ≤ n)
    (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0),
    (∀ p, 0 < ms p) → (∀ p, ms p ≤ 1) → ∀ (x c : ℝ), 1 ≤ c →
    cascadeTiltSq n r ms (fun p => gaussianReal 0 (vs p))
      (fun zs => ENNReal.ofReal (Real.exp
        (parisiLogCoshTerminal 0 (x + ∑ p, zs p))))
      (fun zs => ENNReal.ofReal (Real.tanh (x + ∑ p, zs p) + c)) =
      let A := coleHopfIterate (n - r) (fun p => ms ⟨r + p.val, by omega⟩)
        (fun p => vs ⟨r + p.val, by omega⟩) (parisiLogCoshTerminal 0)
      cascadeTilt r (fun p => ms ⟨p.val, by omega⟩)
        (fun p => gaussianReal 0 (vs ⟨p.val, by omega⟩))
        (fun zs => ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p))))
        (fun zs => ENNReal.ofReal (deriv A (x + ∑ p, zs p) + c) ^ 2) := by
  intro n
  induction n with
  | zero =>
    intro r hr ms vs hpos hle x c hc
    have hr0 : r = 0 := by omega
    subst r
    rw [cascadeTiltSq_zero, cascadeTilt_shiftedTanh_eq ms vs hpos hle x c hc]
    simp
  | succ n ih =>
    intro r hr ms vs hpos hle x c hc
    cases r with
    | zero =>
      rw [cascadeTiltSq_zero, cascadeTilt_shiftedTanh_eq ms vs hpos hle x c hc]
      simp
    | succ r =>
      have hr' : r ≤ n := by omega
      let A := coleHopfIterate (n - r)
        (fun p => ms ⟨r + 1 + p.val, by omega⟩)
        (fun p => vs ⟨r + 1 + p.val, by omega⟩) (parisiLogCoshTerminal 0)
      let pms : Fin (r + 1) → ℝ := fun p => ms ⟨p.val, by omega⟩
      let pvs : Fin (r + 1) → ℝ≥0 := fun p => vs ⟨p.val, by omega⟩
      have hAp : ∀ p : Fin (n - r), 0 < ms ⟨r + 1 + p.val, by omega⟩ :=
        fun p => hpos _
      have hAL := abs_coleHopfIterate_sub_le (n - r)
        (fun p => ms ⟨r + 1 + p.val, by omega⟩)
        (fun p => vs ⟨r + 1 + p.val, by omega⟩)
        (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0)) logCosh_lipschitz
      have hTail : coleHopfIterate n (Fin.tail ms) (Fin.tail vs)
          (parisiLogCoshTerminal 0) =
          coleHopfIterate r (Fin.tail pms) (Fin.tail pvs) A := by
        have hh := coleHopfIterate_split_at_of_le r hr' (Fin.tail ms) (Fin.tail vs)
          (parisiLogCoshTerminal 0)
        have hS : A = coleHopfIterate (n - r)
            (fun p => Fin.tail ms ⟨r + p.val, by omega⟩)
            (fun p => Fin.tail vs ⟨r + p.val, by omega⟩) (parisiLogCoshTerminal 0) := by
          dsimp only [A]
          congr 1 <;> funext p <;> apply congrArg _ <;> apply Fin.ext <;>
            simp only [Fin.val_succ] <;> omega
        rw [hS]
        exact hh
      dsimp only
      have hAeq : coleHopfIterate (n + 1 - (r + 1))
          (fun p => ms ⟨r + 1 + p.val, by omega⟩)
          (fun p => vs ⟨r + 1 + p.val, by omega⟩) (parisiLogCoshTerminal 0) = A := by
        dsimp only [A]
        congr 1
        · omega
        all_goals
          rw [Fin.heq_fun_iff (by omega)]
          intro p
          rfl
      rw [hAeq]
      change _ = cascadeTilt (r + 1) pms (fun p => gaussianReal 0 (pvs p))
        (fun zs => ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p))))
        (fun zs => ENNReal.ofReal (deriv A (x + ∑ p, zs p) + c) ^ 2)
      rw [cascadeTiltSq_succ, cascadeTilt_succ]
      have hW (z : ℝ) :
          cascadeW n ms (fun p => gaussianReal 0 (vs p))
            (fun zs => ENNReal.ofReal (Real.exp
              (parisiLogCoshTerminal 0 (x + ∑ p, zs p)))) z =
          cascadeW r pms (fun p => gaussianReal 0 (pvs p))
            (fun zs => ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p)))) z := by
        rw [cascadeW_gaussian_eq_ofReal_coleHopfQ ms vs hpos logCosh_lipschitz,
          cascadeW_gaussian_eq_ofReal_coleHopfQ pms pvs (fun p => hpos _) hAL,
          hTail]
        rfl
      apply lintegral_congr
      intro z
      rw [hW]
      congr 1
      simp only [Fin.sum_cons, ← add_assoc]
      change cascadeTiltSq n r (Fin.tail ms) (fun p => gaussianReal 0 (Fin.tail vs p))
          (fun zs => ENNReal.ofReal (Real.exp (parisiLogCoshTerminal 0 ((x + z) + ∑ p, zs p))))
          (fun zs => ENNReal.ofReal (Real.tanh ((x + z) + ∑ p, zs p) + c)) = _
      rw [ih r hr' (Fin.tail ms) (Fin.tail vs) (fun p => hpos p.succ)
        (fun p => hle p.succ) (x + z) c hc]
      have hS : coleHopfIterate (n - r)
          (fun p => Fin.tail ms ⟨r + p.val, by omega⟩)
          (fun p => Fin.tail vs ⟨r + p.val, by omega⟩) (parisiLogCoshTerminal 0) = A := by
        dsimp only [A]
        congr 1 <;> funext p <;> dsimp only [Fin.tail]
        all_goals
          apply congrArg _
          apply Fin.ext
          simp only [Fin.val_succ]
          omega
      dsimp only
      rw [hS]
      rfl

/-- The signed conditional square (14.177) is the concrete squared
Cole-Hopf suffix gradient under the normalized prefix law. This is the
pointwise moment identification used in (14.315), with zero variances allowed. -/
theorem cascadeTiltTanhSq_eq_prefix_deriv_sq {n : ℕ}
    (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    (r : ℕ) (hr : r ≤ n) (x : ℝ) :
    cascadeTiltTanhSq ms vs r x =
      let A := coleHopfIterate (n - r) (fun p => ms ⟨r + p.val, by omega⟩)
        (fun p => vs ⟨r + p.val, by omega⟩) (parisiLogCoshTerminal 0)
      ∫ zs, deriv A (x + ∑ p, zs p) ^ 2
        ∂cascadeTiltMeasure r (fun p => ms ⟨p.val, by omega⟩)
          (fun p => gaussianReal 0 (vs ⟨p.val, by omega⟩))
          (fun zs => ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p)))) := by
  let A := coleHopfIterate (n - r) (fun p => ms ⟨r + p.val, by omega⟩)
    (fun p => vs ⟨r + p.val, by omega⟩) (parisiLogCoshTerminal 0)
  let pms : Fin r → ℝ := fun p => ms ⟨p.val, by omega⟩
  let pvs : Fin r → ℝ≥0 := fun p => vs ⟨p.val, by omega⟩
  let G := fun zs : Fin r → ℝ => ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p)))
  let μ := cascadeTiltMeasure r pms (fun p => gaussianReal 0 (pvs p)) G
  have hAL : ∀ y z, |A z - A y| ≤ 1 * |z - y| :=
    abs_coleHopfIterate_sub_le (n - r) _ _
      (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0)) logCosh_lipschitz
  have hAm := (lipschitzWith_toNNReal_of_abs_sub_le hAL).continuous.measurable
  have : IsProbabilityMeasure μ :=
    isProbabilityMeasure_cascadeTiltMeasure_comp_add_sum pms pvs
      (fun p => hpos _) (fun p => hle _) hAm hAL x
  have hD : ∀ y, |deriv A y| ≤ 1 := by
    intro y
    simpa only [Real.norm_eq_abs, Real.toNNReal_one, NNReal.coe_one] using
      (norm_deriv_le_of_lipschitz (x₀ := y) (lipschitzWith_toNNReal_of_abs_sub_le hAL))
  have hsum : Measurable (fun zs : Fin r → ℝ => x + ∑ p, zs p) :=
    measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)
  have hG : Measurable G := (hAm.comp hsum).exp.ennreal_ofReal
  have hDm : Measurable (fun zs : Fin r → ℝ => deriv A (x + ∑ p, zs p)) :=
    (measurable_deriv A).comp hsum
  have hi (c : ℝ) : Integrable (fun zs : Fin r → ℝ =>
      (deriv A (x + ∑ p, zs p) + c) ^ 2) μ := by
    apply Integrable.of_bound ((hDm.add measurable_const).pow_const 2).aestronglyMeasurable
      ((1 + |c|) ^ 2) (.of_forall fun zs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (deriv A (x + ∑ p, zs p) + c) ^ 2 ≤ (1 + |c|) ^ 2
    have hb : |deriv A (x + ∑ p, zs p) + c| ≤ 1 + |c| :=
      (abs_add_le _ _).trans (by linarith [hD (x + ∑ p, zs p)])
    nlinarith [sq_abs (deriv A (x + ∑ p, zs p) + c), abs_nonneg c,
      abs_nonneg (deriv A (x + ∑ p, zs p) + c)]
  have hshift (c : ℝ) (hc : 1 ≤ c) :
      (cascadeTiltSq n r ms (fun p => gaussianReal 0 (vs p))
        (fun zs => ENNReal.ofReal (Real.exp (parisiLogCoshTerminal 0 (x + ∑ p, zs p))))
        (fun zs => ENNReal.ofReal (Real.tanh (x + ∑ p, zs p) + c))).toReal =
      ∫ zs, (deriv A (x + ∑ p, zs p) + c) ^ 2 ∂μ := by
    rw [cascadeTiltSq_shiftedTanh_eq_prefix n r hr ms vs hpos hle x c hc]
    change (cascadeTilt r pms (fun p => gaussianReal 0 (pvs p)) G
      (fun zs => ENNReal.ofReal (deriv A (x + ∑ p, zs p) + c) ^ 2)).toReal = _
    have henc : (fun zs : Fin r → ℝ =>
        ENNReal.ofReal (deriv A (x + ∑ p, zs p) + c) ^ 2) =
        fun zs => ENNReal.ofReal ((deriv A (x + ∑ p, zs p) + c) ^ 2) := by
      funext zs
      rw [ENNReal.ofReal_pow (by linarith [(abs_le.1 (hD (x + ∑ p, zs p))).1])]
    have hobs : Measurable (fun zs : Fin r → ℝ =>
        ENNReal.ofReal ((deriv A (x + ∑ p, zs p) + c) ^ 2)) := by fun_prop
    rw [henc, ← lintegral_cascadeTiltMeasure r pms _ hG hobs]
    exact (integral_eq_lintegral_of_nonneg_ae
      (.of_forall fun zs => sq_nonneg _) (hi c).aestronglyMeasurable).symm
  have h₁ := hshift 1 le_rfl
  have h₂ := hshift 2 (by norm_num)
  simp only [parisiLogCoshTerminal, zero_add] at h₁ h₂
  unfold cascadeTiltTanhSq
  let T := fun c : ℝ => (cascadeTiltSq n r ms (fun p => gaussianReal 0 (vs p))
    (fun zs => ENNReal.ofReal (Real.exp (Real.log (Real.cosh (x + ∑ p, zs p)))))
    (fun zs => ENNReal.ofReal (Real.tanh (x + ∑ p, zs p) + c))).toReal
  change 2 * T 1 - T 2 + 2 = ∫ zs, deriv A (x + ∑ p, zs p) ^ 2 ∂μ
  dsimp only [T]
  rw [h₁, h₂]
  calc
    _ = ∫ zs, 2 * (deriv A (x + ∑ p, zs p) + 1) ^ 2 -
        (deriv A (x + ∑ p, zs p) + 2) ^ 2 + 2 ∂μ := by
      have hlin := integral_add ((hi 1).const_mul 2 |>.sub (hi 2))
        (integrable_const (μ := μ) (2 : ℝ))
      have hsub := integral_sub ((hi 1).const_mul 2) (hi 2)
      simp only [Pi.sub_apply] at hlin hsub
      rw [hlin, hsub, integral_const_mul]
      simp only [integral_const, probReal_univ, one_smul]
    _ = _ := integral_congr_ae (.of_forall fun zs => by ring)

/-- The concrete conditional square is between zero and one. The estimate
is independent of the level count, root field and all Gaussian variances. -/
theorem cascadeTiltTanhSq_mem_Icc {n : ℕ} (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    (r : ℕ) (hr : r ≤ n) (x : ℝ) : cascadeTiltTanhSq ms vs r x ∈ Icc (0 : ℝ) 1 := by
  let A := coleHopfIterate (n - r) (fun p => ms ⟨r + p.val, by omega⟩)
    (fun p => vs ⟨r + p.val, by omega⟩) (parisiLogCoshTerminal 0)
  have hAL : ∀ y z, |A z - A y| ≤ 1 * |z - y| :=
    abs_coleHopfIterate_sub_le (n - r) _ _
      (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0)) logCosh_lipschitz
  have hAm := (lipschitzWith_toNNReal_of_abs_sub_le hAL).continuous.measurable
  have hD : ∀ y, |deriv A y| ≤ 1 := by
    intro y
    simpa only [Real.norm_eq_abs, Real.toNNReal_one, NNReal.coe_one] using
      (norm_deriv_le_of_lipschitz (x₀ := y) (lipschitzWith_toNNReal_of_abs_sub_le hAL))
  rw [cascadeTiltTanhSq_eq_prefix_deriv_sq ms vs hpos hle r hr x]
  constructor
  · exact integral_nonneg fun zs => sq_nonneg _
  · have hb := abs_integral_cascadeTiltMeasure_le
      (fun p : Fin r => ms ⟨p.val, by omega⟩)
      (fun p : Fin r => vs ⟨p.val, by omega⟩) (fun p => hpos _) (fun p => hle _)
      hAm hAL x (f := fun y => deriv A y ^ 2) (C := 1) (fun y => by
        rw [abs_pow]
        simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hD y) 2)
    exact (le_abs_self _).trans hb

/-- Boundedness supplies integrability under every probability-law
evaluation point; no moment assumption on that point is required. -/
theorem integrable_cascadeTiltTanhSq_comp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    (r : ℕ) (hr : r ≤ n) {f : Ω → ℝ} (hf : Measurable f) :
    Integrable (fun ω => cascadeTiltTanhSq ms vs r (f ω)) μ := by
  apply Integrable.of_bound ((measurable_cascadeTiltTanhSq ms vs r).comp hf).aestronglyMeasurable
    1 (.of_forall fun ω => ?_)
  change ‖cascadeTiltTanhSq ms vs r (f ω)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (cascadeTiltTanhSq_mem_Icc ms vs hpos hle r hr _).1]
  exact (cascadeTiltTanhSq_mem_Icc ms vs hpos hle r hr _).2

/-- The independent site-field and root-Gaussian average of the concrete
conditional square can be written as one product-law expectation. -/
theorem integral_cascadeTiltTanhSq_externalField_prod {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {n : ℕ} (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    (r : ℕ) (hr : r ≤ n) (v₀ : ℝ≥0) :
    (∫ h, ∫ a, cascadeTiltTanhSq ms vs r (h + a) ∂gaussianReal 0 v₀ ∂μh) =
      ∫ hz : ℝ × ℝ, cascadeTiltTanhSq ms vs r (hz.1 + hz.2)
        ∂μh.prod (gaussianReal 0 v₀) :=
  (integral_prod _ (integrable_cascadeTiltTanhSq_comp ms vs hpos hle r hr
    (measurable_fst.add measurable_snd))).symm

/-- A prescribed prefix and suffix give the same concrete conditional
square, without casts in the moment consumed by the split-response calculus. -/
theorem cascadeTiltTanhSq_append_eq_prefix_deriv_sq {j s : ℕ}
    (pms : Fin j → ℝ) (pvs : Fin j → ℝ≥0) (sms : Fin s → ℝ) (svs : Fin s → ℝ≥0)
    (hpp : ∀ p, 0 < pms p) (hpl : ∀ p, pms p ≤ 1)
    (hsp : ∀ p, 0 < sms p) (hsl : ∀ p, sms p ≤ 1) (x : ℝ) :
    cascadeTiltTanhSq (Fin.append pms sms) (Fin.append pvs svs) j x =
      ∫ zs, deriv (coleHopfIterate s sms svs (parisiLogCoshTerminal 0))
          (x + ∑ p, zs p) ^ 2
        ∂cascadeTiltMeasure j pms (fun p => gaussianReal 0 (pvs p))
          (fun zs => ENNReal.ofReal (Real.exp
            (coleHopfIterate s sms svs (parisiLogCoshTerminal 0) (x + ∑ p, zs p)))) := by
  have hp : ∀ p, 0 < Fin.append pms sms p := by
    intro p
    refine Fin.addCases (fun q => ?_) (fun q => ?_) p
    · simpa only [Fin.append_left] using hpp q
    · simpa only [Fin.append_right] using hsp q
  have hl : ∀ p, Fin.append pms sms p ≤ 1 := by
    intro p
    refine Fin.addCases (fun q => ?_) (fun q => ?_) p
    · simpa only [Fin.append_left] using hpl q
    · simpa only [Fin.append_right] using hsl q
  have hS : coleHopfIterate (j + s - j)
      (fun p => Fin.append pms sms ⟨j + p.val, by omega⟩)
      (fun p => Fin.append pvs svs ⟨j + p.val, by omega⟩) (parisiLogCoshTerminal 0) =
      coleHopfIterate s sms svs (parisiLogCoshTerminal 0) := by
    congr 1
    · omega
    all_goals
      rw [Fin.heq_fun_iff (by omega)]
      intro p
      have hi : (⟨j + p.val, by omega⟩ : Fin (j + s)) =
          Fin.natAdd j (⟨p.val, by omega⟩ : Fin s) := Fin.ext rfl
      rw [hi, Fin.append_right]
  have hP : (fun p : Fin j => Fin.append pms sms ⟨p.val, by omega⟩) = pms := by
    funext p
    exact Fin.append_left _ _ _
  have hV : (fun p : Fin j => Fin.append pvs svs ⟨p.val, by omega⟩) = pvs := by
    funext p
    exact Fin.append_left _ _ _
  have hh := cascadeTiltTanhSq_eq_prefix_deriv_sq (Fin.append pms sms)
    (Fin.append pvs svs) hp hl j (by omega) x
  dsimp only at hh
  rw [hS, hP] at hh
  have hVG : (fun p : Fin j => gaussianReal 0 (Fin.append pvs svs ⟨p.val, by omega⟩)) =
      fun p => gaussianReal 0 (pvs p) := by
    funext p
    rw [show Fin.append pvs svs ⟨p.val, by omega⟩ = pvs p from congrFun hV p]
  simpa only [hVG] using hh

/-- The Gaussian split in (14.316)-(14.319) gives precisely the actual
first spatial response moment. Matching masses erase the split in the
prefix law, and both closed variance endpoints are included. -/
theorem cascadeTiltTanhSq_split_eq_spatialMoment {j s : ℕ}
    (pms : Fin j → ℝ) (pvs : Fin j → ℝ≥0) (sms : Fin s → ℝ) (svs : Fin s → ℝ≥0)
    (hpp : ∀ p, 0 < pms p) (hpl : ∀ p, pms p ≤ 1)
    (hsp : ∀ p, 0 < sms p) (hsl : ∀ p, sms p ≤ 1)
    {m a v : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (hv : v ∈ Icc (0 : ℝ) a) (x : ℝ) :
    cascadeTiltTanhSq (Fin.append (Fin.snoc pms m) (Fin.cons m sms))
        (Fin.append (Fin.snoc pvs (a - v).toNNReal) (Fin.cons v.toNNReal svs)) (j + 1) x =
      coleHopfIterateSplitSpatialMoment 1 pms pvs m a
        (coleHopfIterate s sms svs (parisiLogCoshTerminal 0)) x v := by
  let A := coleHopfIterate s sms svs (parisiLogCoshTerminal 0)
  let B := coleHopf m v.toNNReal A
  have hAL : ∀ y z, |A z - A y| ≤ 1 * |z - y| :=
    abs_coleHopfIterate_sub_le s sms svs
      (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0)) logCosh_lipschitz
  have hAm := (lipschitzWith_toNNReal_of_abs_sub_le hAL).continuous.measurable
  have hBL := abs_coleHopf_sub_le_of_lipschitz m hAm hAL v.toNNReal
  have hBm : Measurable B := (lipschitzWith_toNNReal_of_abs_sub_le hBL).continuous.measurable
  have hD : ∀ y, |deriv B y| ≤ 1 := by
    intro y
    simpa only [Real.norm_eq_abs, Real.toNNReal_one, NNReal.coe_one] using
      (norm_deriv_le_of_lipschitz (x₀ := y) (lipschitzWith_toNNReal_of_abs_sub_le hBL))
  have hpp' : ∀ p : Fin (j + 1), 0 < Fin.snoc (α := fun _ => ℝ) pms m p := by
    intro p
    exact Fin.lastCases (by simpa using hm) (fun q => by simpa using hpp q) p
  have hpl' : ∀ p : Fin (j + 1), Fin.snoc (α := fun _ => ℝ) pms m p ≤ 1 := by
    intro p
    exact Fin.lastCases (by simpa using hm1) (fun q => by simpa using hpl q) p
  have hsp' : ∀ p : Fin (s + 1), 0 < Fin.cons (α := fun _ => ℝ) m sms p := by
    intro p
    exact Fin.cases (by simpa using hm) (fun q => by simpa using hsp q) p
  have hsl' : ∀ p : Fin (s + 1), Fin.cons (α := fun _ => ℝ) m sms p ≤ 1 := by
    intro p
    exact Fin.cases (by simpa using hm1) (fun q => by simpa using hsl q) p
  have hh := cascadeTiltTanhSq_append_eq_prefix_deriv_sq
    (Fin.snoc pms m) (Fin.snoc pvs (a - v).toNNReal) (Fin.cons m sms)
    (Fin.cons v.toNNReal svs) hpp' hpl' hsp' hsl' x
  simp only [coleHopfIterate_succ, Fin.cons_zero, Fin.tail_cons] at hh
  rw [hh]
  rw [integral_cascadeTiltMeasure_gaussian_snoc pms pvs hpp hpl hBm
    (by simpa only [one_mul] using hBL) hm hm1 (a - v).toNNReal x
    ((measurable_deriv B).pow_const 2) (fun y => by
      rw [abs_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hD y) 2)]
  rw [coleHopfSplit_matching_mass (HasLinearGrowth.of_lipschitz hAL) hAm m hv]
  simp only [coleHopfIterateSplitSpatialMoment, coleHopfSplitSpatialMoment, iteratedDeriv_one]
  rfl

/-- Positive masses for the concrete matched Gaussian split. The two
adjacent Gaussian pieces carry the same old mass, including terminal mass one. -/
def parisiResponseSplitMasses {k : ℕ} (ms : Fin k → ℝ) (p : Fin (k + 1)) :
    Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ :=
  Fin.append (Fin.snoc (parisiOuterMassPrefixMasses ms p) (mExt ms (p.val + 1)))
    (Fin.cons (mExt ms (p.val + 1)) (parisiQSuffixMasses ms p))

/-- The actual total variance is split into a−v and v while every
Gaussian interval before and after it retains its old variance. -/
noncomputable def parisiResponseSplitVars (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (v : ℝ) :
    Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0 :=
  Fin.append (Fin.snoc (parisiOuterMassPrefixVars ξ qs p)
      (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - v).toNNReal)
    (Fin.cons v.toNNReal (parisiQSuffixVars ξ qs p))

/-- Each split coordinate is an old extended mass coordinate; the
matching mass occurs twice at the adjacent Gaussian pieces. -/
theorem parisiResponseSplitMasses_eq_mExt {k : ℕ} (ms : Fin k → ℝ) (p : Fin (k + 1))
    (i : Fin ((p.val + 1) + ((k - p.val) + 1))) :
    parisiResponseSplitMasses ms p i =
      mExt ms (if i.val ≤ p.val then i.val + 1 else i.val) := by
  unfold parisiResponseSplitMasses
  refine Fin.addCases (fun q => ?_) (fun q => ?_) i
  · simp only [Fin.append_left, Fin.val_castAdd, ite_eq_left (by omega : q.val ≤ p.val)]
    refine Fin.lastCases ?_ (fun r => ?_) q
    · simp only [Fin.snoc_last, Fin.val_last]
    · simp only [Fin.snoc_castSucc, Fin.val_castSucc, parisiOuterMassPrefixMasses]
  · simp only [Fin.append_right, Fin.val_natAdd,
      ite_eq_right (by omega : ¬p.val + 1 + q.val ≤ p.val)]
    refine Fin.cases ?_ (fun r => ?_) q
    · simp
    · simp only [Fin.cons_succ, Fin.val_succ, parisiQSuffixMasses]
      congr 1
      omega

/-- The matched split retains monotonicity of the original extended
mass list, as required by the coupled Taylor estimate. -/
theorem parisiResponseSplitMasses_monotone {k : ℕ} (ms : Fin k → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) : Monotone (parisiResponseSplitMasses ms p) := by
  intro i j hij
  rw [parisiResponseSplitMasses_eq_mExt, parisiResponseSplitMasses_eq_mExt]
  apply hm.monotone_mExt
  have hv : i.val ≤ j.val := hij
  split_ifs <;> omega

theorem parisiResponseSplitMasses_pos {k : ℕ} (ms : Fin k → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) : ∀ i, 0 < parisiResponseSplitMasses ms p i := by
  intro i
  unfold parisiResponseSplitMasses
  refine Fin.addCases (fun q => ?_) (fun q => ?_) i
  · rw [Fin.append_left]
    refine Fin.lastCases ?_ (fun r => ?_) q
    · simpa only [Fin.snoc_last] using hm.mExt_pos (by omega : 0 < p.val + 1)
    · simpa only [Fin.snoc_castSucc, parisiOuterMassPrefixMasses] using
        hm.mExt_pos (by omega : 0 < r.val + 1)
  · rw [Fin.append_right]
    refine Fin.cases ?_ (fun r => ?_) q
    · simpa only [Fin.cons_zero] using hm.mExt_pos (by omega : 0 < p.val + 1)
    · simpa only [Fin.cons_succ, parisiQSuffixMasses] using
        hm.mExt_pos (by omega : 0 < p.val + r.val + 2)

theorem parisiResponseSplitMasses_le_one {k : ℕ} (ms : Fin k → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) : ∀ i, parisiResponseSplitMasses ms p i ≤ 1 := by
  intro i
  unfold parisiResponseSplitMasses
  refine Fin.addCases (fun q => ?_) (fun q => ?_) i
  · rw [Fin.append_left]
    refine Fin.lastCases ?_ (fun r => ?_) q
    · simpa only [Fin.snoc_last] using mExt_le_one (fun r => (hm.2.2 r).le) (p.val + 1)
    · simpa only [Fin.snoc_castSucc, parisiOuterMassPrefixMasses] using
        mExt_le_one (fun i => (hm.2.2 i).le) (r.val + 1)
  · rw [Fin.append_right]
    refine Fin.cases ?_ (fun r => ?_) q
    · simpa only [Fin.cons_zero] using mExt_le_one (fun r => (hm.2.2 r).le) (p.val + 1)
    · simpa only [Fin.cons_succ, parisiQSuffixMasses] using
        mExt_le_one (fun i => (hm.2.2 i).le) (p.val + r.val + 2)

/-- Pointwise specialization of (14.322) to the actual Parisi prefix,
old matching mass and actual suffix, with either variance endpoint included. -/
theorem cascadeTiltTanhSq_parisi_split_eq_spatialMoment (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) (x : ℝ) :
    cascadeTiltTanhSq (parisiResponseSplitMasses ms p)
        (parisiResponseSplitVars ξ qs p v) (p.val + 1) x =
      coleHopfIterateSplitSpatialMoment 1 (parisiOuterMassPrefixMasses ms p)
        (parisiOuterMassPrefixVars ξ qs p) (mExt ms (p.val + 1))
        (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))
        (parisiQSuffix ξ 0 ms qs p) x v :=
  cascadeTiltTanhSq_split_eq_spatialMoment
    (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
    (parisiQSuffixMasses ms p) (parisiQSuffixVars ξ qs p)
    (fun i => hm.mExt_pos (by omega)) (fun i => mExt_le_one (fun r => (hm.2.2 r).le) _)
    (fun i => hm.mExt_pos (by omega)) (fun i => mExt_le_one (fun r => (hm.2.2 r).le) _)
    (hm.mExt_pos (by omega)) (mExt_le_one (fun r => (hm.2.2 r).le) _) hv x

/-- The averaged mirror identity (14.315): the coupled conditional square
is the actual outer U moment for every closed admissible split, including the
terminal old mass one. The field and root Gaussian are independent. -/
theorem integral_cascadeTiltTanhSq_parisi_split_eq_left_moment {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) {w : ℝ}
    (hw : w ∈ Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) :
    (∫ h, ∫ z, cascadeTiltTanhSq (parisiResponseSplitMasses ms p)
      (parisiResponseSplitVars ξ qs p
        (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w))
      (p.val + 1) (h + z) ∂gaussianReal 0 (parisiVar ξ qs 0) ∂μh) =
      parisiLeftUSpatialMoment 1 μh ξ ms qs p w := by
  rw [integral_cascadeTiltTanhSq_externalField_prod _ _
    (parisiResponseSplitMasses_pos ms p hm) (parisiResponseSplitMasses_le_one ms p hm)
    (p.val + 1) (by omega)]
  apply integral_congr_ae (.of_forall fun hz => ?_)
  exact cascadeTiltTanhSq_parisi_split_eq_spatialMoment ξ ms qs p hm
    ⟨sub_nonneg.2 hw.2, sub_le_self _ hw.1⟩ (hz.1 + hz.2)

/-- The law-level zero-coupling slope in the mirror split is the actual
outer moment, rather than an assumed response identity. -/
theorem randomFieldPairSiteY₀'_parisi_outer_split_zero_eq {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) {w : ℝ}
    (hw : w ∈ Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) :
    let vs := parisiResponseSplitVars ξ qs p
      (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w)
    randomFieldPairSiteY₀' μh (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p))
        (parisiVar ξ qs 0) vs 0 (couplingFactorSgn 1 (p.val + 2) 0)
        (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) =
      parisiLeftUSpatialMoment 1 μh ξ ms qs p w := by
  dsimp only
  rw [← integral_cascadeTiltTanhSq_parisi_split_eq_left_moment ξ ms qs p hm hw]
  unfold randomFieldPairSiteY₀'
  apply integral_congr_ae (.of_forall fun h => ?_)
  have hh := pairSiteY₀'_coupling_zero (parisiResponseSplitMasses ms p)
    (parisiResponseSplitMasses_pos ms p hm) (parisiResponseSplitMasses_le_one ms p hm)
    (parisiVar ξ qs 0)
    (parisiResponseSplitVars ξ qs p (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w))
    h (τ := p.val + 2) (by omega)
  simpa only [show p.val + 2 - 1 = p.val + 1 by omega] using hh

/-- The averaged version of (14.315) for the mirror orientation follows
from differentiation under the probability field law and the concrete
Gaussian split moment. A finite first field moment suffices. -/
theorem hasDerivAt_randomFieldPairSiteY₀_parisi_outer_split_zero {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) {w : ℝ}
    (hw : w ∈ Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) :
    let vs := parisiResponseSplitVars ξ qs p
      (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w)
    HasDerivAt (fun lam => randomFieldPairSiteY₀ μh
        (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p))
        (parisiVar ξ qs 0) vs lam (couplingFactorSgn 1 (p.val + 2) 0)
        (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)))
      (parisiLeftUSpatialMoment 1 μh ξ ms qs p w) 0 := by
  have hd := hasDerivAt_randomFieldPairSiteY₀_coupling_zero hμ
    (parisiResponseSplitMasses ms p) (parisiResponseSplitMasses_pos ms p hm)
    (parisiResponseSplitMasses_le_one ms p hm) (parisiVar ξ qs 0)
    (parisiResponseSplitVars ξ qs p (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w))
    (τ := p.val + 2) (by omega)
  rw [show p.val + 2 - 1 = p.val + 1 by omega,
    integral_cascadeTiltTanhSq_parisi_split_eq_left_moment ξ ms qs p hm hw] at hd
  exact hd

/-- At a nonterminal old interval, complementary outer and inner
variance coordinates describe the same concrete spatial moment. -/
theorem parisiLeftUSpatialMoment_castSucc_complement_eq_right (s : ℕ)
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (p : Fin k) (v : ℝ) :
    parisiLeftUSpatialMoment s μh ξ ms qs p.castSucc
        (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) - v) =
      parisiRightUSpatialMoment s μh ξ ms qs p v := by
  have hP : parisiOuterMassPrefixMasses ms p.castSucc = parisiMassPrefixMasses ms p := by
    funext i
    exact mExt_val_succ ms (⟨i.val, by omega⟩ : Fin k)
  have hV : parisiOuterMassPrefixVars ξ qs p.castSucc = parisiMassPrefixVars ξ qs p := rfl
  have hR : qExt qs (p.castSucc.val + 2) = qs p.succ := by
    exact qExt_succ_of_lt qs p.succ.isLt
  have hmass : mExt ms (p.castSucc.val + 1) = ms p := mExt_val_succ ms p
  unfold parisiLeftUSpatialMoment parisiRightUSpatialMoment coleHopfIterateOuterSplitSpatialMoment
  rw [hP, hV, hR, hmass]
  simp only [sub_sub_cancel]

/-- The averaged identity (14.315) in the original inner orientation,
with the actual matching mass and its time-varying Gaussian pieces. -/
theorem integral_cascadeTiltTanhSq_parisi_split_eq_right_moment {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) :
    (∫ h, ∫ z, cascadeTiltTanhSq (parisiResponseSplitMasses ms p.castSucc)
      (parisiResponseSplitVars ξ qs p.castSucc v) (p.val + 1) (h + z)
      ∂gaussianReal 0 (parisiVar ξ qs 0) ∂μh) =
      parisiRightUSpatialMoment 1 μh ξ ms qs p v := by
  have hR : qExt qs (p.castSucc.val + 2) = qs p.succ :=
    qExt_succ_of_lt qs p.succ.isLt
  have hw : deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) - v ∈
      Icc (0 : ℝ) (deriv ξ (qExt qs (p.castSucc.val + 2)) - deriv ξ (qs p.castSucc)) := by
    rw [hR]
    exact ⟨sub_nonneg.2 hv.2, sub_le_self _ hv.1⟩
  have hh := integral_cascadeTiltTanhSq_parisi_split_eq_left_moment (μh := μh)
    ξ ms qs p.castSucc hm hw
  rw [parisiLeftUSpatialMoment_castSucc_complement_eq_right, hR, sub_sub_cancel] at hh
  exact hh

/-- At the original Parisi arrays the conditional square is exactly the
initial outer response moment, including the terminal mass one and k=0. -/
theorem cascadeTiltTanhSq_parisi_eq_outer_initial (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (p : Fin (k + 1)) (x : ℝ) :
    cascadeTiltTanhSq (parisiLevelMasses ms) (parisiLevelVars ξ qs) p.val x =
      coleHopfIterateOuterSplitSpatialMoment 1 (parisiOuterMassPrefixMasses ms p)
        (parisiOuterMassPrefixVars ξ qs p) (mExt ms (p.val + 1))
        (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))
        (parisiQSuffix ξ 0 ms qs p) x 0 := by
  have hpos : ∀ i, 0 < parisiLevelMasses ms i := by
    intro i
    rw [parisiLevelMasses_apply]
    exact hm.mExt_pos (by omega)
  have hle : ∀ i, parisiLevelMasses ms i ≤ 1 := by
    intro i
    rw [parisiLevelMasses_apply]
    exact mExt_le_one (fun j => (hm.2.2 j).le) _
  have hS : coleHopfIterate (k + 1 - p.val)
      (fun i => parisiLevelMasses ms ⟨p.val + i.val, by omega⟩)
      (fun i => parisiLevelVars ξ qs ⟨p.val + i.val, by omega⟩)
      (parisiLogCoshTerminal 0) =
      coleHopf (mExt ms (p.val + 1))
        (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p)).toNNReal
        (parisiQSuffix ξ 0 ms qs p) := by
    rw [coleHopfIterate_split_one_of_eq 0 (k - p.val) (by omega)]
    simp only [coleHopfIterate_zero, parisiLevelMasses_apply, parisiLevelVars,
      zero_add, add_zero]
    congr 1
    unfold parisiVar
    rw [qExt_succ_of_lt qs p.isLt]
  have hh := cascadeTiltTanhSq_eq_prefix_deriv_sq (parisiLevelMasses ms)
    (parisiLevelVars ξ qs) hpos hle p.val (by omega) x
  dsimp only at hh
  rw [hS] at hh
  rw [coleHopfIterateOuterSplitSpatialMoment_zero_eq]
  unfold parisiOuterMassPrefixMasses parisiOuterMassPrefixVars
  simpa only [iteratedDeriv_one, parisiLevelMasses_apply, parisiLevelVars,
    parisiOuterMassPrefixMasses, parisiOuterMassPrefixVars] using hh

/-- The pointwise coupled moment identification survives the independent
site-field and root-Gaussian average without any field moment assumption. -/
theorem integral_cascadeTiltTanhSq_parisi_eq_outer_initial (μh : Measure ℝ)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (p : Fin (k + 1)) :
    (∫ hz : ℝ × ℝ, cascadeTiltTanhSq (parisiLevelMasses ms)
      (parisiLevelVars ξ qs) p.val (hz.1 + hz.2)
      ∂μh.prod (gaussianReal 0 (parisiVar ξ qs 0))) =
      parisiLeftUSpatialMoment 1 μh ξ ms qs p 0 :=
  integral_congr_ae (.of_forall fun hz =>
    cascadeTiltTanhSq_parisi_eq_outer_initial ξ ms qs hm p (hz.1 + hz.2))

end SpinGlass
