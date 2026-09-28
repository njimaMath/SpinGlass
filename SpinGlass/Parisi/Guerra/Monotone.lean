import SpinGlass.Parisi.Guerra.Bound

/-!
# Monotone

Extension to nondecreasing mass parameters.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

/-! ### Nondecreasing exponents `0 < m₁ ≤ ⋯ ≤ m_k ≤ 1` -/

omit N in
/-- `ms ↦ 𝔼_a F₁(h + a)` is continuous in the exponents on `(0, 1]^k`: dominated convergence with
the uniform bound `0 ≤ F₁ ≤ |h + a| + ∑ v_p/2` and `continuousOn_parisiRec`. -/
theorem continuousOn_integral_logCoshRec_add (vs : Fin k → ℝ≥0) (h : ℝ) (v₀ : ℝ≥0) :
    ContinuousOn (fun ms : Fin k → ℝ => ∫ a, logCoshRec k ms vs (h + a) ∂gaussianReal 0 v₀)
      (Set.pi Set.univ fun _ => Set.Ioc (0 : ℝ) 1) := by
  intro ms₀ hmem
  have hg : Integrable (fun a : ℝ => |h + a| + ∑ p, (vs p : ℝ) / 2) (gaussianReal 0 v₀) :=
    (((integrable_const h).add (integrable_id_gaussianReal 0 v₀)).abs).add (integrable_const _)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun a => |h + a| + ∑ p, (vs p : ℝ) / 2)
    (Filter.Eventually.of_forall fun ms => ((measurable_logCoshRec k ms vs).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable)
    (eventually_nhdsWithin_of_forall fun ms hms => Filter.Eventually.of_forall fun a => ?_) hg
    (Filter.Eventually.of_forall fun a => ?_)
  · simp only [Set.mem_univ_pi, Set.mem_Ioc] at hms
    rw [Real.norm_eq_abs, abs_of_nonneg (logCoshRec_nonneg k ms vs (fun i => (hms i).1) _)]
    exact logCoshRec_le k ms vs (fun i => (hms i).1) (fun i => (hms i).2) _
  · have hF : Measurable fun y : Fin k → ℝ => Real.log (Real.cosh (h + a + ∑ p, y p)) :=
      Real.measurable_log.comp (Real.continuous_cosh.measurable.comp
        (measurable_const.add (Finset.measurable_sum Finset.univ fun p _ => measurable_pi_apply p)))
    have hfin : ∫⁻ y, ENNReal.ofReal (Real.exp (Real.log (Real.cosh (h + a + ∑ p, y p))))
        ∂Measure.pi (fun p => gaussianReal 0 (vs p)) ≠ ∞ := by
      simp_rw [Real.exp_log (Real.cosh_pos _)]
      rw [lintegral_ofReal_cosh_add_sum_pi_gaussianReal k vs (h + a)]
      exact ENNReal.ofReal_ne_top
    exact (continuousOn_parisiRec k (fun p => gaussianReal 0 (vs p)) hF hfin ms₀ hmem).tendsto

omit N in
lemma continuous_mExt (r : ℕ) : Continuous fun ms : Fin k → ℝ => mExt ms r := by
  by_cases h1 : r = 0
  · simp only [mExt, ite_eq_left h1]
    exact continuous_const
  · by_cases h2 : r - 1 < k
    · simp only [mExt, ite_eq_right h1, dite_eq_left h2]
      exact continuous_apply _
    · simp only [mExt, ite_eq_right h1, dite_eq_right h2]
      exact continuous_const

omit N in
/-- The Parisi functional is continuous in the exponents on `(0, 1]^k`. -/
theorem continuousOn_parisiFunctional (ξ : ℝ → ℝ) (h : ℝ) (qs : Fin (k + 1) → ℝ) :
    ContinuousOn (fun ms : Fin k → ℝ => parisiFunctional ξ h ms qs)
      (Set.pi Set.univ fun _ => Set.Ioc (0 : ℝ) 1) := by
  have h1 := continuousOn_integral_logCoshRec_add k (fun p => parisiVar ξ qs (p.val + 1)) h
    (parisiVar ξ qs 0)
  have h2 : Continuous fun ms : Fin k → ℝ => ∑ p ∈ Finset.range (k + 1),
      mExt ms (p + 1) * (parisiTheta ξ (qExt qs (p + 2)) - parisiTheta ξ (qExt qs (p + 1))) :=
    continuous_finsetSum _ fun p _ => (continuous_mExt k (p + 1)).mul continuous_const
  refine (((continuousOn_const (c := Real.log 2)).add
    (h1.add (continuousOn_const (c := (parisiVar ξ qs (k + 1) : ℝ) / 2)))).sub
    ((continuousOn_const (c := (1 / 2 : ℝ))).mul h2.continuousOn)).congr fun ms hms => ?_
  simp only [Set.mem_univ_pi, Set.mem_Ioc] at hms
  unfold parisiFunctional
  rw [parisiX₀_logCosh_eq k ξ h ms qs (fun i => (hms i).1) (fun i => (hms i).2)]
  rfl

/-- Guerra's bound for nondecreasing exponents `0 < m₁ ≤ ⋯ ≤ m_k ≤ 1`: both sides are
continuous in the exponents and the strictly increasing tuples are dense (Talagrand's remark
after (14.145)). -/
theorem mixedPSpinFreeEnergy_le_parisiFunctional_of_monotone (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (qs : Fin (k + 1) → ℝ) (ms : Fin k → ℝ)
    (h0 : deriv ξ 0 = 0)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (hq01 : ∀ r, qExt qs r ∈ Set.Icc (0 : ℝ) 1)
    (htan : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1, ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (hmsm : Monotone ms) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (h : ℝ) :
    mixedPSpinFreeEnergy N ξ h ≤ parisiFunctional ξ h ms qs :=
  le_of_forall_strictMono_le (f := fun _ => mixedPSpinFreeEnergy N ξ h) continuousOn_const
    (continuousOn_parisiFunctional k ξ h qs)
    (fun ms hsm hpos hlt => mixedPSpinFreeEnergy_le_parisiFunctional N k hN ξ hS qs ms h0 hmono
      hq01 htan hsm hpos hlt h) hmsm hpos hle

/-- The site-vector Guerra bound extends to repeated positive Parisi exponents. -/
theorem siteFieldMixedPSpinFreeEnergy_le_parisiFunctional_of_monotone
    (hN : 0 < N) (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (qs : Fin (k + 1) → ℝ) (ms : Fin k → ℝ) (h0 : deriv ξ 0 = 0)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (hq01 : ∀ r, qExt qs r ∈ Set.Icc (0 : ℝ) 1)
    (htan : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (hmsm : Monotone ms) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (h : Fin N → ℝ) :
    siteFieldMixedPSpinFreeEnergy N ξ h
      ≤ (1 / (N : ℝ)) * ∑ i, parisiFunctional ξ (h i) ms qs :=
  le_of_forall_strictMono_le (f := fun _ => siteFieldMixedPSpinFreeEnergy N ξ h)
    continuousOn_const
    (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
      continuousOn_parisiFunctional k ξ (h i) qs))
    (fun ms hsm hpos hlt => siteFieldMixedPSpinFreeEnergy_le_parisiFunctional N k hN ξ hS
      qs ms h0 hmono hq01 htan hsm hpos hlt h) hmsm hpos hle

/-- Guerra's bound under Talagrand's own hypotheses, for nondecreasing exponents
`0 < m₁ ≤ ⋯ ≤ m_k ≤ 1`. -/
theorem mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn_of_monotone (hN : 0 < N)
    (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef) (hconv : ConvexOn ℝ Set.univ ξ)
    (hdiff : Differentiable ℝ ξ) (h0 : deriv ξ 0 = 0) (qs : Fin (k + 1) → ℝ)
    (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0) (hq1 : qs (Fin.last k) ≤ 1) (ms : Fin k → ℝ)
    (hmsm : Monotone ms) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (h : ℝ) :
    mixedPSpinFreeEnergy N ξ h ≤ parisiFunctional ξ h ms qs :=
  le_of_forall_strictMono_le (f := fun _ => mixedPSpinFreeEnergy N ξ h) continuousOn_const
    (continuousOn_parisiFunctional k ξ h qs)
    (fun ms hsm hpos hlt => mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn N k hN ξ hS
      hconv hdiff h0 qs hqmono hq0 hq1 ms hsm hpos hlt h) hmsm hpos hle

/-- Guerra's bound for the SK model, for nondecreasing exponents `0 < m₁ ≤ ⋯ ≤ m_k ≤ 1`. -/
theorem skFreeEnergy_le_parisiFunctional_of_monotone (hN : 0 < N) (β h : ℝ)
    (qs : Fin (k + 1) → ℝ) (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0) (hq1 : qs (Fin.last k) ≤ 1)
    (ms : Fin k → ℝ) (hmsm : Monotone ms) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    skFreeEnergy N β h ≤ parisiFunctional (skCovXi β) h ms qs := by
  change mixedPSpinFreeEnergy N (skCovXi β) h ≤ _
  exact mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn_of_monotone N k hN (skCovXi β)
    (posSemidef_skCovMatrix N β) (convexOn_univ_skCovXi β) (differentiable_skCovXi β)
    (deriv_skCovXi_zero β) qs hqmono hq0 hq1 ms hmsm hpos hle h

end

end SpinGlass
