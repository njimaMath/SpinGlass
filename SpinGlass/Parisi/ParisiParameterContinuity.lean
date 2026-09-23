import SpinGlass.Parisi.ParisiQDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Parameter continuity for compact Parisi minimization

The variance estimates below are uniform in the spatial argument and in the
external field. This permits averaging against a site law with finite first
moment. The exponent-zero lemma concerns the actual Gaussian expectation
branch of the Cole-Hopf operator, rather than the default value of division
by zero in the positive-mass cascade formula.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- The Gaussian expectation is the continuous extension of the logarithmic
exponential average at exponent zero. This is needed on the compact mass domain. -/
theorem continuous_coleHopf_exponent_local {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (v : ℝ≥0) (x : ℝ) :
    Continuous (fun m : ℝ => coleHopf m v A x) := by
  apply continuous_iff_continuousAt.2
  intro m
  rcases eq_or_ne m 0 with rfl | hm
  · have hI := hasDerivAt_integral_exp_mul_exponent hA hAm v x 0
    have hlog := hI.log (integral_exp_mul_comp_add_pos hA hAm 0 v x).ne'
    have hs := hlog.tendsto_slope
    have hval : (∫ z, Real.exp (0 * A (x + z)) ∂gaussianReal 0 v) = 1 := by simp
    rw [continuousAt_iff_punctured_nhds]
    have heq : (fun m : ℝ => coleHopf m v A x) =ᶠ[𝓝[≠] 0]
        slope (fun m => Real.log (∫ z, Real.exp (m * A (x + z))
          ∂gaussianReal 0 v)) 0 := by
      filter_upwards [self_mem_nhdsWithin] with m hm
      have hm' : m ≠ 0 := hm
      rw [coleHopf_of_ne hm', slope_def_field, hval]
      simp only [Real.log_one, sub_zero, one_div, inv_mul_eq_div]
    rw [coleHopf_zero]
    simpa only [hval, zero_mul, Real.exp_zero, mul_one, integral_const,
      probReal_univ, one_smul, div_one] using hs.congr' heq.symm
  · exact (hasDerivAt_coleHopf_exponent hA hAm hm v x).continuousAt

/-- A symmetric variance bound, including zero variance on either side.
This local adapter avoids choosing an ordering of the two variances downstream. -/
theorem abs_coleHopf_sub_var_le_modulus {A : ℝ → ℝ} {L : ℝ}
    (hAm : Measurable A) (hA : ∀ x y, |A y - A x| ≤ L * |y - x|)
    (m : ℝ) (v w : ℝ≥0) (x : ℝ) :
    |coleHopf m v A x - coleHopf m w A x| ≤
      coleHopfModulus m L (Real.toNNReal |(v : ℝ) - (w : ℝ)|) := by
  rcases le_total w v with hle | hle
  · have heq : Real.toNNReal |(v : ℝ) - (w : ℝ)| = v - w := by
      rw [abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hle)),
        ← NNReal.coe_sub hle, Real.toNNReal_coe]
    rw [heq]
    exact abs_coleHopf_sub_coleHopf_le hAm hA m hle x
  · rw [abs_sub_comm (coleHopf m v A x) (coleHopf m w A x)]
    have heq : Real.toNNReal |(v : ℝ) - (w : ℝ)| = w - v := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hle)),
        ← NNReal.coe_sub hle, Real.toNNReal_coe]
    rw [heq]
    exact abs_coleHopf_sub_coleHopf_le hAm hA m hle x

/-- Changing every Gaussian variance is controlled by the sum of the one-level
moduli. The bound is independent of the value of the terminal function at zero. -/
theorem abs_coleHopfIterate_sub_var_le_sum_modulus
    {G : ℝ → ℝ} {L : ℝ} (hGm : Measurable G)
    (hG : ∀ x y, |G y - G x| ≤ L * |y - x|) (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (vs ws : Fin k → ℝ≥0) (x : ℝ),
      |coleHopfIterate k ms vs G x - coleHopfIterate k ms ws G x| ≤
        ∑ i, coleHopfModulus (ms i) L (Real.toNNReal |(vs i : ℝ) - (ws i : ℝ)|) := by
  induction k with
  | zero => intro ms vs ws x; simp
  | succ k ih =>
    intro ms vs ws x
    let A := coleHopfIterate k (Fin.tail ms) (Fin.tail vs) G
    let B := coleHopfIterate k (Fin.tail ms) (Fin.tail ws) G
    have hAlip := abs_coleHopfIterate_sub_le k (Fin.tail ms) (Fin.tail vs) hGm hG
    have hBlip := abs_coleHopfIterate_sub_le k (Fin.tail ms) (Fin.tail ws) hGm hG
    have hAm := measurable_coleHopfIterate (Fin.tail ms) (Fin.tail vs) hGm hG
    have hBm := measurable_coleHopfIterate (Fin.tail ms) (Fin.tail ws) hGm hG
    have hAB := abs_coleHopf_sub_le_of_sup
      (HasLinearGrowth.of_lipschitz hAlip) hAm
      (HasLinearGrowth.of_lipschitz hBlip) hBm
      (ih (Fin.tail ms) (Fin.tail vs) (Fin.tail ws)) (ms 0) (vs 0) x
    have hv := abs_coleHopf_sub_var_le_modulus hBm hBlip (ms 0) (vs 0) (ws 0) x
    rw [coleHopfIterate_succ, coleHopfIterate_succ, Fin.sum_univ_succ]
    calc
      _ ≤ |coleHopf (ms 0) (vs 0) A x - coleHopf (ms 0) (vs 0) B x| +
          |coleHopf (ms 0) (vs 0) B x - coleHopf (ms 0) (ws 0) B x| := abs_sub_le _ _ _
      _ ≤ _ := by simpa only [Fin.tail] using add_le_add hAB hv |>.trans_eq (add_comm _ _)

/-- All variances, with the plain root expectation at index zero. -/
noncomputable def parisiAllVars (ξ : ℝ → ℝ) {k : ℕ} (qs : Fin (k + 1) → ℝ) :
    Fin (k + 2) → ℝ≥0 := fun p => parisiVar ξ qs p.val

/-- Include the exponent-zero root as a genuine Cole-Hopf level. -/
theorem parisiX₀_eq_coleHopfIterate_all {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (h : ℝ) :
    parisiX₀ ξ ms qs (parisiLogCoshTerminal h) =
      coleHopfIterate (k + 2) (Fin.cons 0 (parisiLevelMasses ms))
        (parisiAllVars ξ qs) (parisiLogCoshTerminal h) 0 := by
  rw [parisiX₀_eq_integral_coleHopfIterate qs hm, coleHopfIterate_succ]
  change (∫ z₀, coleHopfIterate (k + 1) (parisiLevelMasses ms) (parisiLevelVars ξ qs)
    (parisiLogCoshTerminal h) z₀ ∂gaussianReal 0 (parisiVar ξ qs 0)) =
    coleHopf 0 (parisiVar ξ qs 0)
      (coleHopfIterate (k + 1) (parisiLevelMasses ms) (parisiLevelVars ξ qs)
        (parisiLogCoshTerminal h)) 0
  rw [coleHopf_zero]
  simp only [zero_add]

/-- Uniform overlap-parameter control survives the outer random-field average. -/
theorem abs_randomFieldParisiX₀_sub_qs_le_sum_modulus
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs qs₀ : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hμ : Integrable id μh) :
    |randomFieldParisiX₀ μh ξ ms qs - randomFieldParisiX₀ μh ξ ms qs₀| ≤
      ∑ i, coleHopfModulus ((Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms)) i) 1
        (Real.toNNReal |(parisiAllVars ξ qs i : ℝ) - (parisiAllVars ξ qs₀ i : ℝ)|) := by
  unfold randomFieldParisiX₀
  rw [← integral_sub
    (integrable_parisiX₀_logCosh hμ ξ ms qs hm.2.1 (fun i => (hm.2.2 i).le))
    (integrable_parisiX₀_logCosh hμ ξ ms qs₀ hm.2.1 (fun i => (hm.2.2 i).le))]
  have hb := norm_integral_le_of_norm_le_const (μ := μh)
    (f := fun h => parisiX₀ ξ ms qs (parisiLogCoshTerminal h) -
      parisiX₀ ξ ms qs₀ (parisiLogCoshTerminal h))
    (Filter.Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs, parisiX₀_eq_coleHopfIterate_all ms qs hm h,
        parisiX₀_eq_coleHopfIterate_all ms qs₀ hm h]
      exact abs_coleHopfIterate_sub_var_le_sum_modulus
        (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal h))
        (L := 1) (fun x y => by simpa only [one_mul] using
          abs_parisiLogCoshTerminal_sub_le h x y) _ _ _ _ _)
  change |∫ h, parisiX₀ ξ ms qs (parisiLogCoshTerminal h) -
    parisiX₀ ξ ms qs₀ (parisiLogCoshTerminal h) ∂μh| ≤ _
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb

/-- The closed coordinate cube for overlap parameters; no ordering is required
for continuity on this larger set. -/
def parisiOverlapCube (k : ℕ) : Set (Fin (k + 1) → ℝ) :=
  Set.pi Set.univ (fun _ => Icc (0 : ℝ) 1)

theorem mem_parisiOverlapCube_iff {k : ℕ} {qs : Fin (k + 1) → ℝ} :
    qs ∈ parisiOverlapCube k ↔ ∀ i, qs i ∈ Icc (0 : ℝ) 1 := by
  simp only [parisiOverlapCube, Set.mem_pi, Set.mem_univ, forall_true_left]

theorem continuous_qExt_local {k : ℕ} (r : ℕ) :
    Continuous (fun qs : Fin (k + 1) → ℝ => qExt qs r) := by
  unfold qExt
  split_ifs
  · exact continuous_const
  · exact continuous_apply _
  · exact continuous_const

theorem qExt_mem_Icc_of_mem_cube {k : ℕ} {qs : Fin (k + 1) → ℝ}
    (hq : qs ∈ parisiOverlapCube k) (r : ℕ) : qExt qs r ∈ Icc (0 : ℝ) 1 := by
  unfold qExt
  split_ifs
  · simp
  · exact mem_parisiOverlapCube_iff.1 hq _
  · simp

/-- Joint overlap continuity of the quenched recursion follows from the uniform
variance modulus, so no exponential moment of the external field is required. -/
theorem continuousOn_randomFieldParisiX₀_overlapCube
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ) :
    ContinuousOn (fun qs => randomFieldParisiX₀ μh ξ ms qs) (parisiOverlapCube k) := by
  have hd (r : ℕ) : ContinuousOn
      (fun qs : Fin (k + 1) → ℝ => deriv ξ (qExt qs r)) (parisiOverlapCube k) :=
    hξ.deriv_continuous.comp (continuous_qExt_local r).continuousOn
      (fun qs hq => qExt_mem_Icc_of_mem_cube hq r)
  have hv (p : Fin (k + 2)) : ContinuousOn
      (fun qs : Fin (k + 1) → ℝ => (parisiAllVars ξ qs p : ℝ)) (parisiOverlapCube k) := by
    exact (NNReal.continuous_coe.comp continuous_real_toNNReal).comp_continuousOn
      ((hd (p.val + 1)).sub (hd p.val))
  intro qs₀ hq₀
  apply tendsto_iff_dist_tendsto_zero.2
  have hmod (p : Fin (k + 2)) : Tendsto
      (fun qs => coleHopfModulus ((Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms)) p) 1
        (Real.toNNReal |(parisiAllVars ξ qs p : ℝ) - (parisiAllVars ξ qs₀ p : ℝ)|))
      (nhdsWithin qs₀ (parisiOverlapCube k)) (nhds 0) := by
    have he : Tendsto
        (fun qs => |(parisiAllVars ξ qs p : ℝ) - (parisiAllVars ξ qs₀ p : ℝ)|)
        (nhdsWithin qs₀ (parisiOverlapCube k)) (nhds 0) := by
      have hh := ((hv p qs₀ hq₀).sub
        (continuousWithinAt_const (b := (parisiAllVars ξ qs₀ p : ℝ)))).abs
      simpa only [ContinuousWithinAt, Pi.sub_apply, sub_self, abs_zero] using hh
    exact (tendsto_coleHopfModulus _ 1).comp he
  have hsum := tendsto_finsetSum Finset.univ (fun p _ => hmod p)
  simp only [Finset.sum_const_zero] at hsum
  simp only [Real.dist_eq]
  exact squeeze_zero (fun _ => abs_nonneg _)
    (fun qs => abs_randomFieldParisiX₀_sub_qs_le_sum_modulus ms qs qs₀ hm hμ) hsum

/-- Joint continuity of the entire functional on the overlap cube. -/
theorem continuousOn_randomFieldParisiFunctional_overlapCube
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ) :
    ContinuousOn (fun qs => randomFieldParisiFunctional μh ξ ms qs)
      (parisiOverlapCube k) := by
  have htheta : ContinuousOn (parisiTheta ξ) (Icc (0 : ℝ) 1) :=
    (continuousOn_id.mul hξ.deriv_continuous).sub
      (fun x hx => (hξ.hasDeriv x hx).continuousAt.continuousWithinAt)
  have ht (r : ℕ) : ContinuousOn
      (fun qs : Fin (k + 1) → ℝ => parisiTheta ξ (qExt qs r)) (parisiOverlapCube k) :=
    htheta.comp (continuous_qExt_local r).continuousOn
      (fun qs hq => qExt_mem_Icc_of_mem_cube hq r)
  unfold randomFieldParisiFunctional
  exact (continuousOn_const.add
    (continuousOn_randomFieldParisiX₀_overlapCube ms hm hμ hξ)).sub
    (continuousOn_const.mul (continuousOn_finsetSum _ fun p _ =>
      continuousOn_const.mul ((ht (p + 2)).sub (ht (p + 1)))))

/-- The closed nondecreasing overlap domain used before redundant-level removal. -/
def parisiOverlapDomain (k : ℕ) : Set (Fin (k + 1) → ℝ) :=
  parisiOverlapCube k ∩ {qs | Monotone qs}

theorem mem_parisiOverlapDomain_iff {k : ℕ} {qs : Fin (k + 1) → ℝ} :
    qs ∈ parisiOverlapDomain k ↔
      Monotone qs ∧ 0 ≤ qs 0 ∧ qs (Fin.last k) ≤ 1 := by
  constructor
  · rintro ⟨hc, hm⟩
    exact ⟨hm, (mem_parisiOverlapCube_iff.1 hc 0).1,
      (mem_parisiOverlapCube_iff.1 hc (Fin.last k)).2⟩
  · rintro ⟨hm, h0, h1⟩
    refine ⟨mem_parisiOverlapCube_iff.2 (fun i => ?_), hm⟩
    exact ⟨h0.trans (hm (Fin.zero_le i)), (hm (Fin.le_last i)).trans h1⟩

theorem isCompact_parisiOverlapDomain (k : ℕ) : IsCompact (parisiOverlapDomain k) :=
  (isCompact_univ_pi (fun _ : Fin (k + 1) => isCompact_Icc)).inter_right isClosed_monotone

theorem parisiOverlapDomain_nonempty (k : ℕ) : (parisiOverlapDomain k).Nonempty := by
  refine ⟨fun _ => 0, mem_parisiOverlapDomain_iff.2 ?_⟩
  exact ⟨monotone_const, le_refl _, zero_le_one⟩

/-- For fixed admissible masses, the random-field functional attains its minimum
over nondecreasing overlaps. This is compact minimization, not yet full MIN
existence: mass minimization and redundant-level removal are separate obligations. -/
theorem exists_randomFieldParisiQMinimum_of_fixed_masses
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ) :
    ∃ qs ∈ parisiOverlapDomain k,
      IsMinOn (fun qs => randomFieldParisiFunctional μh ξ ms qs) (parisiOverlapDomain k) qs :=
  (isCompact_parisiOverlapDomain k).exists_isMinOn (parisiOverlapDomain_nonempty k)
    ((continuousOn_randomFieldParisiFunctional_overlapCube ms hm hμ hξ).mono
      (fun _ hq => hq.1))

end SpinGlass
