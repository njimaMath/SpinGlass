import SpinGlass.Parisi.ParisiParameterContinuity
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.MeanValue
import Common.Mathlib.MeasureTheory.Integral.LogJensen

/-!
# Continuity of mass parameters at zero

Divided slopes express the Cole-Hopf operator without division by its mass.
This permits simultaneous changes of the mass and the input function on a
closed parameter domain, with a Gaussian integrable domination.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace SpinGlass

theorem continuous_dslope_exp_zero_local : Continuous (dslope Real.exp 0) := by
  apply continuous_iff_continuousAt.2
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · exact continuousAt_dslope_same.2 (Real.differentiableAt_exp)
  · exact (continuousAt_dslope_of_ne hy).2 Real.continuous_exp.continuousAt

/-- A bound for the removable exponential quotient, valid at its diagonal. -/
theorem abs_dslope_exp_zero_le (y : ℝ) :
    |dslope Real.exp 0 y| ≤ Real.exp |y| := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [Real.deriv_exp]
  · have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := Real.exp) (s := Icc (-|y|) |y|) (C := Real.exp |y|) (x := 0) (y := y)
      (fun _ _ => Real.differentiableAt_exp)
      (fun z hz => by
        rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 hz.2)
      (convex_Icc _ _) (by simp [abs_nonneg]) (by
        exact ⟨neg_abs_le y, le_abs_self y⟩)
    rw [dslope_of_ne _ hy, slope_def_field]
    simp only [sub_zero, Real.exp_zero, Real.norm_eq_abs] at h ⊢
    rw [abs_div]
    exact (div_le_iff₀ (abs_pos.2 hy)).2 h

/-- The numerator quotient at mass zero is its actual expectation integrand. -/
theorem integrable_coleHopf_exponent_kernel {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    Integrable (fun z => A (x + z) * dslope Real.exp 0 (m * A (x + z)))
      (gaussianReal 0 v) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simpa [Real.deriv_exp] using
      (hA.toHasExpGrowth.comp_add_const x).integrable_gaussianReal
        (hAm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  · have heq : (fun z => A (x + z) * dslope Real.exp 0 (m * A (x + z))) =
        (fun z => (Real.exp (m * A (x + z)) - 1) / m) := by
      funext z
      apply (eq_div_iff hm).2
      have h := sub_smul_dslope Real.exp 0 (m * A (x + z))
      simpa only [sub_zero, smul_eq_mul, Real.exp_zero, mul_assoc, mul_comm m] using h
    rw [heq]
    exact ((integrable_exp_mul_comp_add hA hAm m v x).sub
      (integrable_const (1 : ℝ))).div_const m

/-- Cole-Hopf in a form that is valid without dividing by the mass.
The diagonal values are derivatives of exponential and logarithm. -/
theorem coleHopf_eq_dslope_log_mul_integral {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    coleHopf m v A x =
      dslope Real.log 1 (∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v) *
        ∫ z, A (x + z) * dslope Real.exp 0 (m * A (x + z)) ∂gaussianReal 0 v := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [Real.deriv_exp, Real.deriv_log]
  · have hi : m * (∫ z, A (x + z) * dslope Real.exp 0 (m * A (x + z))
        ∂gaussianReal 0 v) = (∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v) - 1 := by
      rw [← integral_const_mul]
      calc
        _ = ∫ z, Real.exp (m * A (x + z)) - 1 ∂gaussianReal 0 v := by
          apply integral_congr_ae
          exact Eventually.of_forall fun z => by
            have h := sub_smul_dslope Real.exp 0 (m * A (x + z))
            simpa only [sub_zero, smul_eq_mul, Real.exp_zero, mul_assoc] using h
        _ = _ := by
          rw [integral_sub (integrable_exp_mul_comp_add hA hAm m v x) (integrable_const 1)]
          simp
    have hl := sub_smul_dslope Real.log 1
      (∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v)
    simp only [smul_eq_mul, Real.log_one, sub_zero] at hl
    rw [coleHopf_of_ne hm]
    apply (mul_left_cancel₀ hm)
    calc
      _ = Real.log (∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v) := by field_simp
      _ = _ := by rw [← hl, ← hi]; ring

theorem abs_mul_dslope_exp_le {w m C B : ℝ}
    (_hC : 0 ≤ C) (hB : 0 ≤ B) (hw : |w| ≤ C) (hm : |m| ≤ B) :
    |w * dslope Real.exp 0 (m * w)| ≤ Real.exp ((B + 1) * C) := by
  have hwe : |w| ≤ Real.exp C := by linarith [Real.add_one_le_exp C]
  have hmw : |m * w| ≤ B * C := by
    rw [abs_mul]
    exact mul_le_mul hm hw (abs_nonneg _) hB
  rw [abs_mul]
  calc
    _ ≤ Real.exp C * Real.exp (B * C) :=
      mul_le_mul hwe ((abs_dslope_exp_zero_le _).trans (Real.exp_le_exp.2 hmw))
        (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem continuousOn_dslope_log_one_local :
    ContinuousOn (dslope Real.log 1) (Ioi (0 : ℝ)) := by
  intro y hy
  apply ContinuousAt.continuousWithinAt
  rcases eq_or_ne y 1 with rfl | hy1
  · exact continuousAt_dslope_same.2 (Real.differentiableAt_log (by norm_num))
  · exact (continuousAt_dslope_of_ne hy1).2
      (Real.continuousAt_log (ne_of_gt hy))

/-- Simultaneous mass and input-function continuity, including mass zero.
The uniform linear bound is only required on the indicated parameter domain.
No exponential moment of a site-field law is involved. -/
theorem continuousOn_coleHopf_family_local {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E]
    {s : Set E} {A : E → ℝ → ℝ} {m : E → ℝ} {a b B : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hAm : ∀ p ∈ s, Measurable (A p))
    (hAc : ∀ z, ContinuousOn (fun p => A p z) s)
    (hmc : ContinuousOn m s)
    (hbound : ∀ p ∈ s, ∀ z, |A p z| ≤ a + b * |z|)
    (hm : ∀ p ∈ s, |m p| ≤ B) (v : ℝ≥0) (x : ℝ) :
    ContinuousOn (fun p => coleHopf (m p) v (A p) x) s := by
  let a' := a + b * |x|
  let bound := fun z : ℝ => Real.exp ((B + 1) * a') * Real.exp ((B + 1) * b * |z|)
  have ha' : 0 ≤ a' := by dsimp [a']; positivity
  have hshift : ∀ p ∈ s, ∀ z, |A p (x + z)| ≤ a' + b * |z| := by
    intro p hp z
    calc
      _ ≤ a + b * |x + z| := hbound p hp _
      _ ≤ a + b * (|x| + |z|) := by gcongr; exact abs_add_le _ _
      _ = _ := by dsimp [a']; ring
  have hbi : Integrable bound (gaussianReal 0 v) :=
    (integrable_exp_mul_abs_gaussianReal 0 v ((B + 1) * b)).const_mul _
  have heq : ∀ z, Real.exp ((B + 1) * (a' + b * |z|)) = bound z := by
    intro z
    dsimp [bound]
    rw [← Real.exp_add]
    congr 1
    ring
  have hI : ContinuousOn (fun p => ∫ z, Real.exp (m p * A p (x + z))
      ∂gaussianReal 0 v) s := by
    refine continuousOn_of_dominated
      (bound := bound)
      (fun p hp => (Real.measurable_exp.comp
        (measurable_const.mul ((hAm p hp).comp
          (measurable_const.add measurable_id)))).aestronglyMeasurable)
      ?_ hbi ?_
    · intro p hp
      exact Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← heq]
        apply Real.exp_le_exp.2
        calc
          m p * A p (x + z) ≤ |m p| * |A p (x + z)| := by
            rw [← abs_mul]; exact le_abs_self _
          _ ≤ B * (a' + b * |z|) :=
            mul_le_mul (hm p hp) (hshift p hp z) (abs_nonneg _) hB
          _ ≤ _ := by nlinarith [abs_nonneg z]
    · exact Eventually.of_forall fun z => Real.continuous_exp.comp_continuousOn
        (hmc.mul (hAc (x + z)))
  have hJ : ContinuousOn (fun p => ∫ z, A p (x + z) *
      dslope Real.exp 0 (m p * A p (x + z)) ∂gaussianReal 0 v) s := by
    refine continuousOn_of_dominated (bound := bound)
      (fun p hp => (((hAm p hp).comp (measurable_const.add measurable_id)).mul
        (continuous_dslope_exp_zero_local.measurable.comp (measurable_const.mul
          ((hAm p hp).comp (measurable_const.add measurable_id))))).aestronglyMeasurable)
      ?_ hbi ?_
    · intro p hp
      exact Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, ← heq]
        exact abs_mul_dslope_exp_le (by positivity) hB (hshift p hp z) (hm p hp)
    · exact Eventually.of_forall fun z => (hAc (x + z)).mul
        (continuous_dslope_exp_zero_local.comp_continuousOn (hmc.mul (hAc (x + z))))
  have hlog := continuousOn_dslope_log_one_local.comp hI (fun p hp =>
    integral_exp_mul_comp_add_pos (⟨a, b, hb, hbound p hp⟩ : HasLinearGrowth (A p))
      (hAm p hp) (m p) v x)
  exact (hlog.mul hJ).congr fun p hp =>
    coleHopf_eq_dslope_log_mul_integral ⟨a, b, hb, hbound p hp⟩ (hAm p hp) (m p) v x

/-- A closed box for all finite mass coordinates, including zero. -/
def parisiMassBox (k : ℕ) (B : ℝ) : Set (Fin k → ℝ) :=
  Set.pi univ (fun _ => Icc (-B) B)

theorem mem_parisiMassBox_iff {k : ℕ} {B : ℝ} {ms : Fin k → ℝ} :
    ms ∈ parisiMassBox k B ↔ ∀ i, |ms i| ≤ B := by
  simp only [parisiMassBox, mem_univ_pi, mem_Icc, abs_le]

theorem isCompact_parisiMassBox (k : ℕ) (B : ℝ) : IsCompact (parisiMassBox k B) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

/-- The finite Gaussian recursion is jointly continuous in all its masses on
a closed bounded box. Zero masses use the ordinary Gaussian expectation. -/
theorem continuousOn_coleHopfIterate_masses_local {G : ℝ → ℝ} {L B : ℝ}
    (hGm : Measurable G) (hG : ∀ x y, |G y - G x| ≤ L * |y - x|)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (k : ℕ) :
    ∀ (vs : Fin k → ℝ≥0) (x : ℝ),
      ContinuousOn (fun ms => coleHopfIterate k ms vs G x) (parisiMassBox k B) := by
  induction k with
  | zero => intro vs x; simpa using (continuousOn_const (c := G x))
  | succ k ih =>
    intro vs x
    let A := fun ms : Fin (k + 1) → ℝ =>
      coleHopfIterate k (Fin.tail ms) (Fin.tail vs) G
    have htail : MapsTo (Fin.tail : (Fin (k + 1) → ℝ) → (Fin k → ℝ))
        (parisiMassBox (k + 1) B) (parisiMassBox k B) := by
      intro ms hms
      exact mem_parisiMassBox_iff.2 fun i => (mem_parisiMassBox_iff.1 hms) i.succ
    have htc : Continuous (Fin.tail : (Fin (k + 1) → ℝ) → (Fin k → ℝ)) :=
      continuous_pi fun i => continuous_apply i.succ
    have hAc : ∀ z, ContinuousOn (fun ms => A ms z) (parisiMassBox (k + 1) B) :=
      fun z => (ih (Fin.tail vs) z).comp htc.continuousOn htail
    obtain ⟨c, hc⟩ := (isCompact_parisiMassBox k B).bddAbove_image
      ((ih (Fin.tail vs) 0).abs)
    have hbound : ∀ ms ∈ parisiMassBox (k + 1) B, ∀ z,
        |A ms z| ≤ max c 0 + L * |z| := by
      intro ms hms z
      have h0 : |A ms 0| ≤ max c 0 :=
        (hc (mem_image_of_mem _ (htail hms))).trans (le_max_left _ _)
      have hz := abs_coleHopfIterate_sub_le k (Fin.tail ms) (Fin.tail vs) hGm hG 0 z
      change |A ms z - A ms 0| ≤ L * |z - 0| at hz
      calc
        |A ms z| ≤ |A ms z - A ms 0| + |A ms 0| := by
          simpa using abs_add_le (A ms z - A ms 0) (A ms 0)
        _ ≤ _ := by simpa only [sub_zero] using add_le_add hz h0 |>.trans_eq (add_comm _ _)
    have hcont := continuousOn_coleHopf_family_local (le_max_right c 0) hL hB
      (fun ms _ => measurable_coleHopfIterate (Fin.tail ms) (Fin.tail vs) hGm hG)
      hAc (continuous_apply (0 : Fin (k + 1))).continuousOn hbound
      (fun ms hms => mem_parisiMassBox_iff.1 hms 0) (vs 0) x
    simpa only [coleHopfIterate_succ] using hcont

/-- The lower Jensen bound includes the ordinary expectation branch. -/
theorem integral_le_coleHopf_of_nonneg_mass_local {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) {m : ℝ} (hm : 0 ≤ m)
    (v : ℝ≥0) (x : ℝ) :
    (∫ z, A (x + z) ∂gaussianReal 0 v) ≤ coleHopf m v A x := by
  rcases eq_or_lt_of_le hm with he | hp
  · subst m; rw [coleHopf_zero]
  · have hAi : Integrable (fun z => A (x + z)) (gaussianReal 0 v) :=
      (hA.toHasExpGrowth.comp_add_const x).integrable_gaussianReal
        (hAm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    have hlog : Integrable (fun z => Real.log (Real.exp (m * A (x + z))))
        (gaussianReal 0 v) := by simpa only [Real.log_exp] using hAi.const_mul m
    have h := integral_log_le_log_integral
      (Eventually.of_forall fun z => Real.exp_pos (m * A (x + z)))
      (integrable_exp_mul_comp_add hA hAm m v x) hlog
    simp only [Real.log_exp, integral_const_mul] at h
    rw [coleHopf_of_ne hp.ne', one_div, inv_mul_eq_div]
    exact (le_div_iff₀ hp).2 (by simpa only [mul_comm] using h)

theorem coleHopf_le_mass_one_local {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (v : ℝ≥0) (x : ℝ) : coleHopf m v A x ≤ coleHopf 1 v A x := by
  rcases eq_or_lt_of_le hm.1 with he | hp
  · subst m
    rw [coleHopf_zero]
    exact integral_le_coleHopf_of_nonneg_mass_local hA hAm zero_le_one v x
  · simpa only [coleHopf_of_ne one_ne_zero, one_div_one, one_mul, one_mul] using
      coleHopf_le_log_integral_exp hA hAm hp hm.2 v x

/-- A single variance modulus works uniformly for all masses in `[0,1]`. -/
theorem coleHopfModulus_le_mass_one_local {m L : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (v : ℝ≥0) : coleHopfModulus m L v ≤ coleHopfModulus 1 L v := by
  have hpos := coleHopf_le_mass_one_local (hasLinearGrowth_const_mul_abs L)
    (measurable_const_mul_abs L) hm v 0
  have hneg := integral_le_coleHopf_of_nonneg_mass_local
    (hasLinearGrowth_const_mul_abs (-L)) (measurable_const_mul_abs (-L)) hm.1 v 0
  have hmean := integral_le_coleHopf_of_nonneg_mass_local
    (hasLinearGrowth_const_mul_abs L) (measurable_const_mul_abs L) zero_le_one v 0
  have heq : (∫ z, -L * |0 + z| ∂gaussianReal 0 v) =
      -(∫ z, L * |0 + z| ∂gaussianReal 0 v) := by
    simp only [neg_mul, integral_neg]
  rw [heq] at hneg
  unfold coleHopfModulus
  apply max_le
  · exact hpos.trans (le_max_left _ _)
  · exact (by linarith : -coleHopf m v (fun t => -L * |t|) 0 ≤
      coleHopf 1 v (fun t => L * |t|) 0).trans (le_max_left _ _)

/-- Joint continuity of mass and Gaussian variance lists on a closed parameter
domain. The terminal function may be any measurable Lipschitz function. -/
theorem continuousOn_coleHopfIterate_parameters_local
    {E : Type*} [TopologicalSpace E] [FirstCountableTopology E]
    {s : Set E} {G : ℝ → ℝ} {L : ℝ} {k : ℕ}
    {ms : E → Fin k → ℝ} {vs : E → Fin k → ℝ≥0}
    (hGm : Measurable G) (hG : ∀ x y, |G y - G x| ≤ L * |y - x|) (hL : 0 ≤ L)
    (hmc : ContinuousOn ms s) (hvc : ContinuousOn vs s)
    (hm : ∀ p ∈ s, ∀ i, ms p i ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    ContinuousOn (fun p => coleHopfIterate k (ms p) (vs p) G x) s := by
  intro p₀ hp₀
  apply tendsto_iff_dist_tendsto_zero.2
  have hmb : MapsTo ms s (parisiMassBox k 1) := by
    intro p hp
    exact mem_parisiMassBox_iff.2 fun i => by
      rw [abs_of_nonneg (hm p hp i).1]
      exact (hm p hp i).2
  have hf := ((continuousOn_coleHopfIterate_masses_local hGm hG hL zero_le_one
      k (vs p₀) x).comp hmc hmb) p₀ hp₀
  have hmass : Tendsto
      (fun p => |coleHopfIterate k (ms p) (vs p₀) G x -
        coleHopfIterate k (ms p₀) (vs p₀) G x|) (𝓝[s] p₀) (𝓝 0) := by
    simpa only [Function.comp_apply, Pi.sub_apply, sub_self, abs_zero] using
      (hf.sub (continuousWithinAt_const (b :=
        coleHopfIterate k (ms p₀) (vs p₀) G x))).abs.tendsto
  have hmod (i : Fin k) : Tendsto
      (fun p => coleHopfModulus 1 L (Real.toNNReal |(vs p i : ℝ) - (vs p₀ i : ℝ)|))
      (𝓝[s] p₀) (𝓝 0) := by
    have hv := ((NNReal.continuous_coe.comp (continuous_apply i)).comp_continuousOn hvc)
      p₀ hp₀
    have he : Tendsto (fun p => |(vs p i : ℝ) - (vs p₀ i : ℝ)|) (𝓝[s] p₀) (𝓝 0) := by
      simpa only [Function.comp_apply, Pi.sub_apply, sub_self, abs_zero] using
        (hv.sub (continuousWithinAt_const (b := (vs p₀ i : ℝ)))).abs.tendsto
    exact (tendsto_coleHopfModulus 1 L).comp he
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hmod i)
  simp only [Finset.sum_const_zero] at hsum
  simp only [Real.dist_eq]
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
    ?_ (by simpa using hmass.add hsum)
  filter_upwards [self_mem_nhdsWithin] with p hp
  have hv := abs_coleHopfIterate_sub_var_le_sum_modulus hGm hG k (ms p) (vs p) (vs p₀) x
  have hu : (∑ i, coleHopfModulus (ms p i) L
      (Real.toNNReal |(vs p i : ℝ) - (vs p₀ i : ℝ)|)) ≤
      ∑ i, coleHopfModulus 1 L (Real.toNNReal |(vs p i : ℝ) - (vs p₀ i : ℝ)|) :=
    Finset.sum_le_sum fun i _ => coleHopfModulus_le_mass_one_local (hm p hp i) _
  simp only [Real.toNNReal_abs] at hv hu
  calc
    _ ≤ |coleHopfIterate k (ms p) (vs p) G x - coleHopfIterate k (ms p) (vs p₀) G x| +
        |coleHopfIterate k (ms p) (vs p₀) G x - coleHopfIterate k (ms p₀) (vs p₀) G x| :=
      abs_sub_le _ _ _
    _ ≤ _ := by
      calc
        _ ≤ (∑ i, coleHopfModulus 1 L
            (Real.nnabs ((vs p i : ℝ) - (vs p₀ i : ℝ)))) +
            |coleHopfIterate k (ms p) (vs p₀) G x -
              coleHopfIterate k (ms p₀) (vs p₀) G x| :=
          add_le_add_left (hv.trans hu) _
        _ = _ := add_comm _ _

end SpinGlass
