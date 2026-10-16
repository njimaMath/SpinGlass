import SpinGlass.Parisi.Interpolation.FixedWeightIdentity
import SpinGlass.Parisi.Interpolation.Bracket
import SpinGlass.Parisi.Coupled.CoupledParisiCorrection

/-!
# Averaging the Guerra bound on any interpolation interval

The weight expectation is constant in the field and time. Its value
is the slope of the original interpolation bracket.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

variable (N k : ℕ)

theorem measurable_guerraBound_joint (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) :
    Measurable (fun q : ((Fin N → ℝ) × CascadeWeights k) × ℝ =>
      guerraBound N k ξ qs q.1.1 q.1.2 q.2) := by
  let G := fun a : ℝ × ((EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ)) =>
    hamG N k a.1 a.2.2 a.2.1.1 a.2.1.2
  have hG : Measurable (Function.uncurry G) := by
    unfold Function.uncurry G hamG branchZX branchHamX
    fun_prop
  have hmap : Measurable (fun q : (((Fin N → ℝ) × CascadeWeights k) × ℝ) ×
      (EnergySpace N × MarksSpace N k) =>
        ((q.1.2, ((q.2.1, q.2.2.1), q.1.1.1)), cascadeZip k (q.1.1.2, q.2.2.2))) :=
    (measurable_fst.snd.prodMk
      ((measurable_snd.fst.prodMk measurable_snd.snd.fst).prodMk measurable_fst.fst.fst)).prodMk
      ((measurable_cascadeZip k).comp (measurable_fst.fst.snd.prodMk measurable_snd.snd.snd))
  have hp (r : ℕ) : Measurable (fun q : (((Fin N → ℝ) × CascadeWeights k) × ℝ) ×
      (EnergySpace N × MarksSpace N k) =>
        gibbsPair k r (hamG N k q.1.2 q.1.1.1 q.2.1 q.2.2.1) q.1.1.2 q.2.2.2) := by
    have hn := (measurable_cascadeSq_prod k r hG).comp hmap
    have hd := (measurable_cascadeSum_prod k hG).comp hmap
    exact (hn.mul (hd.inv.pow_const 2)).ennreal_toReal
  have hh : Measurable (fun q : (((Fin N → ℝ) × CascadeWeights k) × ℝ) ×
      (EnergySpace N × MarksSpace N k) =>
        levelBound k (ξ 1 - deriv ξ (qs (Fin.last k)))
          (fun r => parisiTheta ξ (qExt qs (r + 1)))
          (fun r => gibbsPair k r (hamG N k q.1.2 q.1.1.1 q.2.1 q.2.2.1)
            q.1.1.2 q.2.2.2)) :=
    measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun r _ =>
      measurable_const.mul ((hp r).sub (hp (r + 1)))))
  exact hh.stronglyMeasurable.integral_prod_right'.measurable

theorem integrable_guerraBound_prod_time
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (a b : ℝ) :
    Integrable (fun q : ((Fin N → ℝ) × CascadeWeights k) × ℝ =>
      guerraBound N k ξ qs q.1.1 q.1.2 q.2)
      (((externalFieldVecLaw N μh).prod (cascadeWeightsLaw k ms)).prod
        (volume.restrict (Ioc a b))) := by
  let : IsFiniteMeasure (volume.restrict (Ioc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  exact Integrable.of_bound (measurable_guerraBound_joint N k ξ qs).aestronglyMeasurable _
    (Filter.Eventually.of_forall fun q => norm_guerraBound_le N k ξ qs q.1.1 q.1.2 q.2)

theorem integral_guerraBound_prod_eq
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (qs : Fin (k + 1) → ℝ) (t : ℝ) :
    (∫ q : (Fin N → ℝ) × CascadeWeights k, guerraBound N k ξ qs q.1 q.2 t
      ∂(externalFieldVecLaw N μh).prod (cascadeWeightsLaw k ms)) =
      (1 / 2) * (ξ 1 - deriv ξ (qs (Fin.last k))) +
        (1 / 2) * ∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1)) *
          (mExt ms (r + 1) - mExt ms r) := by
  have hmap : Measurable (fun q : (Fin N → ℝ) × CascadeWeights k => (q, t)) :=
    measurable_id.prodMk measurable_const
  have hm' : Measurable (fun q : (Fin N → ℝ) × CascadeWeights k =>
      guerraBound N k ξ qs q.1 q.2 t) := by
    have hh := (measurable_guerraBound_joint N k ξ qs).comp hmap
    simp only [Function.comp_def] at hh
    exact hh
  have hi : Integrable (fun q : (Fin N → ℝ) × CascadeWeights k =>
      guerraBound N k ξ qs q.1 q.2 t)
      ((externalFieldVecLaw N μh).prod (cascadeWeightsLaw k ms)) :=
    Integrable.of_bound hm'.aestronglyMeasurable _ (Filter.Eventually.of_forall fun q =>
      norm_guerraBound_le N k ξ qs q.1 q.2 t)
  rw [integral_prod _ hi]
  simp_rw [integral_guerraBound N k ξ qs _ ms hm.1 hm.2.1 hm.2.2 t]
  rw [integral_const, probReal_univ, one_smul]

theorem integral_intervalIntegral_guerraBound_prod_eq
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (qs : Fin (k + 1) → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ q : (Fin N → ℝ) × CascadeWeights k,
      (∫ t in a..b, guerraBound N k ξ qs q.1 q.2 t)
      ∂(externalFieldVecLaw N μh).prod (cascadeWeightsLaw k ms)) =
      ((1 / 2) * (ξ 1 - deriv ξ (qs (Fin.last k))) +
        (1 / 2) * ∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1)) *
          (mExt ms (r + 1) - mExt ms r)) * (b - a) := by
  simp_rw [intervalIntegral.integral_of_le hab]
  rw [integral_integral_swap (integrable_guerraBound_prod_time N k μh ξ ms qs a b)]
  simp_rw [integral_guerraBound_prod_eq N k μh ξ ms hm qs]
  rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]
  simp only [smul_eq_mul, mul_comm]

omit N in
theorem averagedGuerraBound_eq_bracket_slope
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) :
    (1 / 2) * (ξ 1 - deriv ξ (qs (Fin.last k))) +
      (1 / 2) * ∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1)) *
        (mExt ms (r + 1) - mExt ms r) =
      ((parisiVar ξ qs (k + 1) : ℝ) - parisiCorrection ξ ms qs) / 2 := by
  have hv : (parisiVar ξ qs (k + 1) : ℝ) = deriv ξ 1 - deriv ξ (qs (Fin.last k)) := by
    have hn := hξ.strictMonoOn_deriv.monotoneOn (hq.mem_Icc (Fin.last k))
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩) (hq.mem_Icc _).2
    rw [parisiVar, qExt_of_le qs (by omega), qExt_succ_of_lt qs (Nat.lt_succ_self k)]
    change ((deriv ξ 1 - deriv ξ (qs (Fin.last k))).toNNReal : ℝ) = _
    exact Real.coe_toNNReal _ (sub_nonneg.2 hn)
  have hs : (∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1)) *
      (mExt ms (r + 1) - mExt ms r)) =
      ∑ r : Fin (k + 1), parisiTheta ξ (qs r) * (mExt ms (r.val + 1) - mExt ms r.val) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun r _ => by rw [qExt_succ_of_lt qs r.isLt]
  rw [hs, hv, parisiCorrection_eq_theta_fin_sum]
  unfold parisiTheta
  ring

end

end SpinGlass
