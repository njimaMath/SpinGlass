import SpinGlass.Parisi.Guerra.GuerraFixedWeights
import Common.Mathlib.Analysis.Convex.TangentLine
import Common.Mathlib.Probability.PointProcess.CascadeExponent

/-!
# LogCosh

The Gaussian log-cosh recursion and its integrability.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

/-! ### The recursion for `log cosh` with Gaussian marks -/

/-- `F₁` for `F_{k+1}(y₁, …, y_k) = log cosh (a + ∑ₚ yₚ)`, `yₚ ∼ N(0, vₚ)`. -/
def logCoshRec (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (a : ℝ) : ℝ :=
  parisiRec k ms (fun p => gaussianReal 0 (vs p)) (fun y => Real.log (Real.cosh (a + ∑ p, y p)))

omit N in
lemma lintegral_ofReal_cosh_add_sum_pi_gaussianReal (vs : Fin k → ℝ≥0) (a : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.cosh (a + ∑ p, y p)) ∂Measure.pi (fun p => gaussianReal 0 (vs p))
      = ENNReal.ofReal (Real.cosh a * Real.exp (∑ p, (vs p : ℝ) / 2)) := by
  have h1 : ∀ y : Fin k → ℝ, ENNReal.ofReal (Real.cosh (a + ∑ p, y p))
      = ENNReal.ofReal (Real.exp a / 2) * ENNReal.ofReal (Real.exp (∑ p, 1 * y p))
        + ENNReal.ofReal (Real.exp (-a) / 2) * ENNReal.ofReal (Real.exp (∑ p, (-1) * y p)) := by
    intro y
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    simp_rw [one_mul, neg_one_mul, Finset.sum_neg_distrib]
    rw [Real.cosh_eq, Real.exp_add, neg_add, Real.exp_add]
    ring
  simp_rw [h1]
  have hm : ∀ c : ℝ, Measurable fun y : Fin k → ℝ => ENNReal.ofReal (Real.exp (∑ p, c * y p)) :=
    fun c => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (Finset.measurable_sum _ fun p _ => measurable_const.mul (measurable_pi_apply p)))
  rw [lintegral_add_left ((hm 1).const_mul _), lintegral_const_mul _ (hm 1),
    lintegral_const_mul _ (hm (-1)), lintegral_ofReal_exp_sum_mul_pi_gaussianReal,
    lintegral_ofReal_exp_sum_mul_pi_gaussianReal]
  simp only [one_pow, mul_one, neg_one_sq]
  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.cosh_eq]
  ring

omit N in
lemma measurable_ofReal_exp_log_cosh_add_sum (a : ℝ) :
    Measurable fun y : Fin k → ℝ =>
      ENNReal.ofReal (Real.exp (Real.log (Real.cosh (a + ∑ p, y p)))) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Real.measurable_log.comp
    (Real.continuous_cosh.measurable.comp (measurable_const.add
      (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)))))

omit N in
lemma measurable_logCoshRec (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) :
    Measurable (logCoshRec k ms vs) := by
  unfold logCoshRec parisiRec
  refine Real.measurable_log.comp (ENNReal.measurable_toReal.comp ?_)
  have hc : Continuous fun q : ℝ × (Fin k → ℝ) =>
      ENNReal.ofReal (Real.exp (Real.log (Real.cosh (q.1 + ∑ p, q.2 p)))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      ((Real.continuous_cosh.comp (continuous_fst.add (continuous_finsetSum _ fun p _ =>
        (continuous_apply p).comp continuous_snd))).log fun q => (Real.cosh_pos _).ne'))
  have hu : Measurable (Function.uncurry fun (a : ℝ) (y : Fin k → ℝ) =>
      ENNReal.ofReal (Real.exp (Real.log (Real.cosh (a + ∑ p, y p))))) := by
    have := hc.measurable
    unfold Function.uncurry
    exact this
  have := measurable_cascadeRec_prod k ms (fun p => gaussianReal 0 (vs p)) hu
  exact this

omit N in
lemma logCoshRec_nonneg (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i) (a : ℝ) :
    0 ≤ logCoshRec k ms vs a :=
  parisiRec_nonneg k ms _ (fun _ => log_cosh_nonneg _) hpos

omit N in
lemma cascadeRec_cosh_ne_top (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1) (a : ℝ) :
    cascadeRec k ms (fun p => gaussianReal 0 (vs p))
      (fun y => ENNReal.ofReal (Real.exp (Real.log (Real.cosh (a + ∑ p, y p))))) ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_
    (cascadeRec_le_lintegral_pi k ms _ (measurable_ofReal_exp_log_cosh_add_sum k a) hpos hle)
  simp_rw [Real.exp_log (Real.cosh_pos _)]
  rw [lintegral_ofReal_cosh_add_sum_pi_gaussianReal]
  exact ENNReal.ofReal_ne_top

omit N in
/-- Jensen's bound `F₁ ≤ log 𝔼 exp F_{k+1} = log cosh a + ∑ₚ vₚ/2 ≤ |a| + ∑ₚ vₚ/2`. -/
lemma logCoshRec_le (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1) (a : ℝ) :
    logCoshRec k ms vs a ≤ |a| + ∑ p, (vs p : ℝ) / 2 := by
  unfold logCoshRec parisiRec
  have hG := measurable_ofReal_exp_log_cosh_add_sum k a
  have hJ := cascadeRec_le_lintegral_pi k ms (fun p => gaussianReal 0 (vs p)) hG hpos hle
  have hI : ∫⁻ y, ENNReal.ofReal (Real.exp (Real.log (Real.cosh (a + ∑ p, y p))))
      ∂Measure.pi (fun p => gaussianReal 0 (vs p))
      = ENNReal.ofReal (Real.cosh a * Real.exp (∑ p, (vs p : ℝ) / 2)) := by
    simp_rw [Real.exp_log (Real.cosh_pos _)]
    exact lintegral_ofReal_cosh_add_sum_pi_gaussianReal k vs a
  rw [hI] at hJ
  have hpos' := cascadeRec_pos k ms (fun p => gaussianReal 0 (vs p)) hG
    (fun _ => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos
  calc Real.log (cascadeRec k ms (fun p => gaussianReal 0 (vs p))
        (fun y => ENNReal.ofReal (Real.exp (Real.log (Real.cosh (a + ∑ p, y p)))))).toReal
      ≤ Real.log (ENNReal.ofReal (Real.cosh a * Real.exp (∑ p, (vs p : ℝ) / 2))).toReal :=
        Real.log_le_log (ENNReal.toReal_pos hpos'.ne'
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hJ)) (ENNReal.toReal_mono ENNReal.ofReal_ne_top hJ)
    _ = Real.log (Real.cosh a) + ∑ p, (vs p : ℝ) / 2 := by
        rw [ENNReal.toReal_ofReal (by positivity),
          Real.log_mul (Real.cosh_pos _).ne' (Real.exp_pos _).ne', Real.log_exp]
    _ ≤ |a| + ∑ p, (vs p : ℝ) / 2 := add_le_add (log_cosh_le_abs a) le_rfl

omit N in
lemma integrable_logCoshRec_add (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1) (h : ℝ) (v₀ : ℝ≥0) :
    Integrable (fun a => logCoshRec k ms vs (h + a)) (gaussianReal 0 v₀) := by
  have hg : Integrable (fun a : ℝ => |h + a| + ∑ p, (vs p : ℝ) / 2) (gaussianReal 0 v₀) :=
    (((integrable_const h).add (integrable_id_gaussianReal 0 v₀)).abs).add (integrable_const _)
  refine Integrable.mono' hg
    ((measurable_logCoshRec k ms vs).comp (measurable_const.add measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (logCoshRec_nonneg k ms vs hpos _)]
  exact logCoshRec_le k ms vs hpos hle _

omit N in
/-- The absorption of the level `m_{k+1} = 1` (Talagrand's (14.84)) in terms of `logCoshRec`. -/
lemma logCoshRec_eq_parisiRecGauss (ξ : ℝ → ℝ) (h : ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (a : ℝ) :
    logCoshRec k ms (fun p => parisiVar ξ qs (p.val + 1)) (h + a)
      = parisiRecGauss ξ ms qs (fun x => Real.log (Real.cosh (h + x))) a
        - (parisiVar ξ qs (k + 1) : ℝ) / 2 := by
  rw [parisiRecGauss_logCosh ξ h ms qs hpos hle a]
  unfold logCoshRec
  have : (fun p : Fin k => parisiMarks ξ qs p.castSucc)
      = fun p => gaussianReal 0 (parisiVar ξ qs (p.val + 1)) := by
    funext p
    rfl
  rw [this]
  ring

omit N in
/-- `X₀` as the `z₀`-average of the recursion over the levels `1, …, k` plus the absorbed level
(14.84). -/
lemma parisiX₀_logCosh_eq (ξ : ℝ → ℝ) (h : ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x)))
      = (∫ a, logCoshRec k ms (fun p => parisiVar ξ qs (p.val + 1)) (h + a)
          ∂gaussianReal 0 (parisiVar ξ qs 0)) + (parisiVar ξ qs (k + 1) : ℝ) / 2 := by
  have hpt : ∀ a, parisiRecGauss ξ ms qs (fun x => Real.log (Real.cosh (h + x))) a
      = logCoshRec k ms (fun p => parisiVar ξ qs (p.val + 1)) (h + a)
        + (parisiVar ξ qs (k + 1) : ℝ) / 2 := by
    intro a
    rw [logCoshRec_eq_parisiRecGauss k ξ h ms qs hpos hle a]
    ring
  unfold parisiX₀
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_add (integrable_logCoshRec_add k ms _ hpos hle h _) (integrable_const _),
    integral_const, probReal_univ, one_smul]

/-- The `z₀`-average of the site sum: `N` times the Gaussian average of `F₁`. -/
lemma integral_sum_logCoshRec (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1) (h : Fin N → ℝ) (v₀ : ℝ≥0) :
    ∫ z₀, ∑ i, logCoshRec k ms vs (h i + z₀ i) ∂Measure.pi (fun _ : Fin N => gaussianReal 0 v₀)
      = ∑ i, ∫ a, logCoshRec k ms vs (h i + a) ∂gaussianReal 0 v₀ := by
  have hmp : ∀ i : Fin N, MeasurePreserving (Function.eval i)
      (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀)) (gaussianReal 0 v₀) := fun i =>
    measurePreserving_eval (μ := fun _ : Fin N => gaussianReal 0 v₀) i
  have hint_i : ∀ i : Fin N, Integrable
      (fun z₀ : Fin N → ℝ => logCoshRec k ms vs (h i + z₀ i))
      (Measure.pi fun _ : Fin N => gaussianReal 0 v₀) := fun i =>
    ((hmp i).integrable_comp ((measurable_logCoshRec k ms vs).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable).2
        (integrable_logCoshRec_add k ms vs hpos hle (h i) v₀)
  rw [integral_finsetSum _ fun i _ => hint_i i]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : Measurable (fun a : ℝ => logCoshRec k ms vs (h i + a)) :=
    (measurable_logCoshRec k ms vs).comp (measurable_const.add measurable_id)
  have hi := integral_map (μ := Measure.pi fun _ : Fin N => gaussianReal 0 v₀)
    (hmp i).measurable.aemeasurable hm.aestronglyMeasurable
  rw [(hmp i).map_eq] at hi
  exact hi.symm

/-- The site factorization (14.82) with the constant `log 2`:
`F₁ = N log 2 + ∑ᵢ F₁(z_{i,0})` for `F_{k+1} = ∑ᵢ log (2 cosh (h i + z_{i,0} + ∑ₚ x_{i,p}))`. -/
theorem parisiRec_coshF (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1) (h : Fin N → ℝ) (z₀ : Fin N → ℝ) :
    parisiRec k ms (gaussianMarks N k vs) (coshF N k h z₀)
      = N * Real.log 2 + ∑ i, logCoshRec k ms vs (h i + z₀ i) := by
  have hFs : ∀ i : Fin N, Measurable fun y : Fin k → ℝ =>
      Real.log (2 * Real.cosh (h i + z₀ i + ∑ p, y p)) := fun i =>
    Real.measurable_log.comp (measurable_const.mul (Real.continuous_cosh.measurable.comp
      (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))))
  have hfin : ∀ i : Fin N, cascadeRec k ms (fun p => gaussianReal 0 (vs p))
      (fun y => ENNReal.ofReal (Real.exp (Real.log (2 * Real.cosh (h i + z₀ i + ∑ p, y p))))) ≠ ∞ := by
    intro i
    refine ne_top_of_le_ne_top ?_ (cascadeRec_le_lintegral_pi k ms _
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hFs i))) hpos hle)
    have hm : Measurable fun y : Fin k → ℝ => ENNReal.ofReal (Real.cosh (h i + z₀ i + ∑ p, y p)) :=
      ENNReal.measurable_ofReal.comp (Real.continuous_cosh.measurable.comp
        (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)))
    simp_rw [Real.exp_log (by positivity : (0 : ℝ) < 2 * Real.cosh _),
      ENNReal.ofReal_mul (zero_le_two : (0 : ℝ) ≤ 2)]
    rw [lintegral_const_mul _ hm, lintegral_ofReal_cosh_add_sum_pi_gaussianReal]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have h1 := parisiRec_sum k ms (fun p _ => gaussianReal 0 (vs p))
    (Fs := fun i y => Real.log (2 * Real.cosh (h i + z₀ i + ∑ p, y p))) hFs hpos hfin
  beta_reduce at h1
  have h2 : ∀ i : Fin N, parisiRec k ms (fun p => gaussianReal 0 (vs p))
      (fun y => Real.log (2 * Real.cosh (h i + z₀ i + ∑ p, y p)))
      = Real.log 2 + logCoshRec k ms vs (h i + z₀ i) := by
    intro i
    have hmi : Measurable fun y : Fin k → ℝ => Real.log (Real.cosh (h i + z₀ i + ∑ p, y p)) :=
      Real.measurable_log.comp (Real.continuous_cosh.measurable.comp
        (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)))
    have h3 := parisiRec_const_add k ms (fun p => gaussianReal 0 (vs p))
      (F := fun y : Fin k → ℝ => Real.log (Real.cosh (h i + z₀ i + ∑ p, y p))) hmi hpos
      (cascadeRec_cosh_ne_top k ms vs hpos hle (h i + z₀ i)) (Real.log 2)
    have hfun : (fun y : Fin k → ℝ => Real.log (2 * Real.cosh (h i + z₀ i + ∑ p, y p)))
        = fun y => Real.log 2 + Real.log (Real.cosh (h i + z₀ i + ∑ p, y p)) := by
      funext y
      rw [Real.log_mul two_ne_zero (Real.cosh_pos _).ne']
    rw [hfun, h3]
    rfl
  unfold coshF
  refine h1.trans ?_
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]


end

end SpinGlass
