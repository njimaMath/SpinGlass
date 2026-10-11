import SpinGlass.Parisi.Variational.ParisiMassDerivative

/-!
# Uniform control through an ordered mass prefix

For increasing masses in [0,1], the logarithm of the cascade density has a
telescoping perturbation bound independent of the number of levels. This is
an alternative to the cascade representation in the proof of Talagrand,
Vol. II, Proposition 14.7.10. Centered single-layer estimates then remain
uniform after propagation, without exponential moments of the site field.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace SpinGlass

/-- The actual logarithm of the product of the Gaussian cascade weights. -/
noncomputable def coleHopfIterateTiltLog : (j : ℕ) → (Fin j → ℝ) →
    (Fin j → ℝ≥0) → (ℝ → ℝ) → ℝ → (Fin j → ℝ) → ℝ
  | 0, _, _, _, _, _ => 0
  | j + 1, ms, vs, G, x, zs =>
      ms 0 * (coleHopfIterate j (Fin.tail ms) (Fin.tail vs) G (x + zs 0) -
        coleHopfIterate (j + 1) ms vs G x) +
      coleHopfIterateTiltLog j (Fin.tail ms) (Fin.tail vs) G (x + zs 0) (Fin.tail zs)

private theorem cascadeW_gaussian_eq_exp {j : ℕ}
    (ms : Fin (j + 1) → ℝ) (vs : Fin (j + 1) → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) {G : ℝ → ℝ}
    (hG : ∀ x y, |G y - G x| ≤ 1 * |y - x|) (x z : ℝ) :
    (cascadeW j ms (fun i => gaussianReal 0 (vs i))
      (fun zs => ENNReal.ofReal (Real.exp (G (x + ∑ i, zs i)))) z).toReal =
      Real.exp (ms 0 * (coleHopfIterate j (Fin.tail ms) (Fin.tail vs) G (x + z) -
        coleHopfIterate (j + 1) ms vs G x)) := by
  have hGm := (lipschitzWith_toNNReal_of_abs_sub_le hG).continuous.measurable
  have hcons : (fun ys : Fin j → ℝ =>
      ENNReal.ofReal (Real.exp (G (x + ∑ i, Fin.cons z ys i)))) =
      fun ys => ENNReal.ofReal (Real.exp (G ((x + z) + ∑ i, ys i))) := by
    funext ys
    rw [Fin.sum_cons]
    congr 3
    ring
  rw [cascadeW, hcons]
  change (((cascadeRec j (Fin.tail ms) (fun i => gaussianReal 0 (Fin.tail vs i))
      (fun ys => ENNReal.ofReal (Real.exp (G ((x + z) + ∑ i, ys i))))) /
    cascadeRec (j + 1) ms (fun i => gaussianReal 0 (vs i))
      (fun zs => ENNReal.ofReal (Real.exp (G (x + ∑ i, zs i))))) ^ ms 0).toReal = _
  rw [
    cascadeRec_gaussian_comp_add_sum j (Fin.tail ms) (Fin.tail vs)
      (fun i => hpos i.succ) hGm hG (x + z),
    cascadeRec_gaussian_comp_add_sum (j + 1) ms vs hpos hGm hG x,
    ← ENNReal.toReal_rpow, ENNReal.toReal_div]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [← Real.exp_sub, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

/-- Identify the signed density used by the actual mass derivative with
the exponential of its concrete logarithmic recursion. -/
theorem cascadeTiltDensity_gaussian_eq_exp_tiltLog (j : ℕ) :
    ∀ (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0), (∀ i, 0 < ms i) →
      ∀ {G : ℝ → ℝ}, (∀ x y, |G y - G x| ≤ 1 * |y - x|) → ∀ x zs,
        (cascadeTiltDensity j ms (fun i => gaussianReal 0 (vs i))
          (fun ys => ENNReal.ofReal (Real.exp (G (x + ∑ i, ys i)))) zs).toReal =
        Real.exp (coleHopfIterateTiltLog j ms vs G x zs) := by
  induction j with
  | zero => intro ms vs hpos G hG x zs; simp [coleHopfIterateTiltLog]
  | succ j ih =>
    intro ms vs hpos G hG x zs
    have hcons : (fun ys : Fin j → ℝ =>
        ENNReal.ofReal (Real.exp (G (x + ∑ i, Fin.cons (zs 0) ys i)))) =
        fun ys => ENNReal.ofReal (Real.exp (G ((x + zs 0) + ∑ i, ys i))) := by
      funext ys
      rw [Fin.sum_cons]
      congr 3
      ring
    change (cascadeW j ms (fun i => gaussianReal 0 (vs i))
        (fun ys => ENNReal.ofReal (Real.exp (G (x + ∑ i, ys i)))) (zs 0) *
      cascadeTiltDensity j (Fin.tail ms) (fun i => gaussianReal 0 (Fin.tail vs i))
        (fun ys => ENNReal.ofReal (Real.exp (G (x + ∑ i, Fin.cons (zs 0) ys i))))
        (Fin.tail zs)).toReal = _
    rw [ENNReal.toReal_mul, cascadeW_gaussian_eq_exp ms vs hpos hG,
      hcons, ih (Fin.tail ms) (Fin.tail vs) (fun i => hpos i.succ) hG
        (x + zs 0) (Fin.tail zs), ← Real.exp_add]
    rfl

private theorem abs_tiltLog_sub_add_le (j : ℕ) :
    ∀ (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0), Monotone ms →
      (∀ i, ms i ≤ 1) → ∀ {G H : ℝ → ℝ},
      (∀ x y, |G y - G x| ≤ 1 * |y - x|) →
      (∀ x y, |H y - H x| ≤ 1 * |y - x|) → ∀ {δ : ℝ}, 0 ≤ δ →
      (∀ y, |H y - G y| ≤ δ) → ∀ {a : ℝ}, 0 ≤ a → a ≤ 1 →
      (∀ i, a ≤ ms i) → ∀ x zs,
        |coleHopfIterateTiltLog j ms vs H x zs - coleHopfIterateTiltLog j ms vs G x zs +
          a * (coleHopfIterate j ms vs H x - coleHopfIterate j ms vs G x)| ≤
          (2 - a) * δ := by
  induction j with
  | zero =>
    intro ms vs hmono hle G H hG hH δ hδ hsup a ha ha1 hal x zs
    simp only [coleHopfIterateTiltLog, coleHopfIterate_zero, sub_self, zero_add]
    rw [abs_mul, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left (hsup x) ha).trans (by nlinarith)
  | succ j ih =>
    intro ms vs hmono hle G H hG hH δ hδ hsup a ha ha1 hal x zs
    have hm0 : 0 ≤ ms 0 := ha.trans (hal 0)
    have htail := ih (Fin.tail ms) (Fin.tail vs)
      (fun i t hit => hmono (Fin.succ_le_succ_iff.2 hit))
      (fun i => hle i.succ) hG hH hδ hsup hm0 (hle 0)
      (fun i => hmono (Fin.zero_le _)) (x + zs 0) (Fin.tail zs)
    have hroot := abs_coleHopfIterate_sub_le_of_sup ms vs
      (lipschitzWith_toNNReal_of_abs_sub_le hH).continuous.measurable hH
      (lipschitzWith_toNNReal_of_abs_sub_le hG).continuous.measurable hG hsup x
    have hdiff : 0 ≤ ms 0 - a := sub_nonneg.2 (hal 0)
    have hterm : |(ms 0 - a) * (coleHopfIterate (j + 1) ms vs H x -
        coleHopfIterate (j + 1) ms vs G x)| ≤ (ms 0 - a) * δ := by
      rw [abs_mul, abs_of_nonneg hdiff]
      exact mul_le_mul_of_nonneg_left hroot hdiff
    have heq : coleHopfIterateTiltLog (j + 1) ms vs H x zs -
        coleHopfIterateTiltLog (j + 1) ms vs G x zs +
        a * (coleHopfIterate (j + 1) ms vs H x - coleHopfIterate (j + 1) ms vs G x) =
      (coleHopfIterateTiltLog j (Fin.tail ms) (Fin.tail vs) H (x + zs 0) (Fin.tail zs) -
        coleHopfIterateTiltLog j (Fin.tail ms) (Fin.tail vs) G (x + zs 0) (Fin.tail zs) +
        ms 0 * (coleHopfIterate j (Fin.tail ms) (Fin.tail vs) H (x + zs 0) -
          coleHopfIterate j (Fin.tail ms) (Fin.tail vs) G (x + zs 0))) -
        (ms 0 - a) * (coleHopfIterate (j + 1) ms vs H x -
          coleHopfIterate (j + 1) ms vs G x) := by
      simp only [coleHopfIterateTiltLog]
      ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)

/-- The logarithmic cascade-density perturbation is at most twice the input
perturbation, regardless of the number of ordered mass levels. This avoids
a sum of separate level bounds in Proposition 14.7.10. -/
theorem abs_coleHopfIterateTiltLog_sub_le_of_sup {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (hmono : Monotone ms)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) {G H : ℝ → ℝ}
    (hG : ∀ x y, |G y - G x| ≤ 1 * |y - x|)
    (hH : ∀ x y, |H y - H x| ≤ 1 * |y - x|) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsup : ∀ y, |H y - G y| ≤ δ) (x : ℝ) (zs : Fin j → ℝ) :
    |coleHopfIterateTiltLog j ms vs H x zs - coleHopfIterateTiltLog j ms vs G x zs| ≤
      2 * δ := by
  simpa only [zero_mul, add_zero, sub_zero] using
    abs_tiltLog_sub_add_le j ms vs hmono hle hG hH hδ hsup
      (a := 0) le_rfl zero_le_one (fun i => (hpos i).le) x zs

private lemma abs_exp_sub_le {r s : ℝ} :
    |Real.exp r - Real.exp s| ≤ Real.exp s * Real.exp |r - s| * |r - s| := by
  have h := (convex_Icc (-|r - s|) |r - s|).norm_image_sub_le_of_norm_deriv_le
    (f := Real.exp) (C := Real.exp |r - s|)
    (fun _ _ => Real.differentiableAt_exp)
    (fun t ht => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 ht.2)
    (x := 0) (y := r - s)
    ⟨neg_nonpos.2 (abs_nonneg _), abs_nonneg _⟩ ⟨neg_abs_le _, le_abs_self _⟩
  simp only [Real.norm_eq_abs, Real.exp_zero, sub_zero] at h
  have he : Real.exp r = Real.exp s * Real.exp (r - s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, ← mul_sub_one, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le |>.trans_eq (by ring)

/-- A bounded input perturbation changes the actual cascade density by a
relative bound independent of the number of ordered levels. -/
theorem abs_cascadeTiltDensity_gaussian_sub_le_of_sup {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (hmono : Monotone ms)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) {G H : ℝ → ℝ}
    (hG : ∀ x y, |G y - G x| ≤ 1 * |y - x|)
    (hH : ∀ x y, |H y - H x| ≤ 1 * |y - x|) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsup : ∀ y, |H y - G y| ≤ δ) (x : ℝ) (zs : Fin j → ℝ) :
    |(cascadeTiltDensity j ms (fun i => gaussianReal 0 (vs i))
        (fun ys => ENNReal.ofReal (Real.exp (H (x + ∑ i, ys i)))) zs).toReal -
      (cascadeTiltDensity j ms (fun i => gaussianReal 0 (vs i))
        (fun ys => ENNReal.ofReal (Real.exp (G (x + ∑ i, ys i)))) zs).toReal| ≤
      (cascadeTiltDensity j ms (fun i => gaussianReal 0 (vs i))
        (fun ys => ENNReal.ofReal (Real.exp (G (x + ∑ i, ys i)))) zs).toReal *
        Real.exp (2 * δ) * (2 * δ) := by
  simp only [cascadeTiltDensity_gaussian_eq_exp_tiltLog j ms vs hpos hG,
    cascadeTiltDensity_gaussian_eq_exp_tiltLog j ms vs hpos hH]
  have h := abs_coleHopfIterateTiltLog_sub_le_of_sup ms vs hmono hpos hle hG hH hδ hsup x zs
  exact abs_exp_sub_le.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h) (Real.exp_pos _).le) h
    (abs_nonneg _) (by positivity))

/-- The mass derivative of a propagated layer is Lipschitz in mass with a
coefficient depending only on V, independent of the ordered prefix length.
This is the uniformity input to Proposition 14.7.10 for arbitrary fields. -/
theorem exists_uniform_coleHopfIterateMassDeriv_lipschitz_bound (V : ℝ≥0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (j : ℕ) (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0),
      Monotone ms → (∀ i, 0 < ms i) → (∀ i, ms i ≤ 1) →
      ∀ (A : ℝ → ℝ), Measurable A → (∀ x y, |A y - A x| ≤ |y - x|) →
      ∀ (v : ℝ≥0), v ≤ V → ∀ x, ∀ b ∈ Icc (0 : ℝ) 1, ∀ m ∈ Icc (0 : ℝ) 1,
        |coleHopfIterateMassDeriv ms vs v A b x - coleHopfIterateMassDeriv ms vs v A m x| ≤
          M * |b - m| := by
  obtain ⟨C, hC, hfirst⟩ := exists_uniform_coleHopf_mass_first_derivative_bound V
  obtain ⟨L, hL, hsecond⟩ := exists_uniform_coleHopf_mass_second_derivative_bound V
  let M := L + 2 * C ^ 2 * Real.exp (2 * C)
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro j ms vs hmono hpos hle A hAm hLip v hv x b hb m hm
  have hLip' : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hAg := HasLinearGrowth.of_lipschitz hLip'
  have hD : ∀ c ∈ Icc (0 : ℝ) 1, ∀ y, |coleHopfMassDeriv c v A y| ≤ C := by
    intro c hc y
    rw [← (hasDerivAt_coleHopf_mass hAg hAm v y c).deriv]
    exact (hfirst A hAm hLip v hv y).2.1 c ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have hGdiff : ∀ y, |coleHopf b v A y - coleHopf m v A y| ≤ C * |b - m| := by
    intro y
    have hh := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun c _ => (hasDerivAt_coleHopf_mass hAg hAm v y c).differentiableAt)
      (fun c hc => by
        rw [Real.norm_eq_abs, (hasDerivAt_coleHopf_mass hAg hAm v y c).deriv]
        exact hD c hc y) hm hb
    simpa only [Real.norm_eq_abs] using hh
  have hDdiff : ∀ y, |coleHopfMassDeriv b v A y - coleHopfMassDeriv m v A y| ≤
      L * |b - m| := by
    intro y
    rw [← (hasDerivAt_coleHopf_mass hAg hAm v y b).deriv,
      ← (hasDerivAt_coleHopf_mass hAg hAm v y m).deriv]
    have hh := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (f := deriv (fun c => coleHopf c v A y))
      (fun c _ => (analyticAt_coleHopf_mass hAg hAm v y c).deriv.differentiableAt)
      (fun c hc => by simpa only [Real.norm_eq_abs] using (hsecond A hAm hLip v hv y).2 c hc)
      hm hb
    simpa only [Real.norm_eq_abs] using hh
  let G := fun (c : ℝ) (zs : Fin j → ℝ) =>
    ENNReal.ofReal (Real.exp (coleHopf c v A (x + ∑ i, zs i)))
  let ρ := fun c zs => (cascadeTiltDensity j ms (fun i => gaussianReal 0 (vs i)) (G c) zs).toReal
  let μ := Measure.pi (fun i => gaussianReal 0 (vs i))
  have hGlip : ∀ c, ∀ y z, |coleHopf c v A z - coleHopf c v A y| ≤ 1 * |z - y| :=
    fun c => abs_coleHopf_sub_le_of_lipschitz c hAm hLip' v
  have hGm : ∀ c, Measurable (G c) := by
    intro c
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((lipschitzWith_toNNReal_of_abs_sub_le (hGlip c)).continuous.measurable.comp
        (measurable_const.add (Finset.measurable_sum _ fun i _ => measurable_pi_apply i))))
  have hGp : ∀ c zs, 0 < G c zs := fun c zs => ENNReal.ofReal_pos.2 (Real.exp_pos _)
  have hGfin : ∀ c, ∫⁻ zs, G c zs ∂μ ≠ ∞ := fun c =>
    lintegral_ofReal_exp_comp_add_sum_pi_gaussianReal_ne_top vs (hGlip c) x
  have hρ : ∀ c, Integrable (ρ c) μ := fun c =>
    integrable_toReal_cascadeTiltDensity j ms _ (hGm c) (hGp c) hpos hle (hGfin c)
  have hρint : ∀ c, ∫ zs, ρ c zs ∂μ = 1 := by
    intro c
    have := isProbabilityMeasure_cascadeTiltMeasure j ms _ (hGm c) (hGp c) hpos hle (hGfin c)
    have hh := integral_cascadeTiltMeasure j ms _ (hGm c) (hGp c) hpos hle (hGfin c)
      (fun _ => (1 : ℝ))
    simpa only [smul_eq_mul, mul_one, integral_const, probReal_univ, one_smul] using hh.symm
  have hρdiff : ∀ zs, |ρ b zs - ρ m zs| ≤
      ρ m zs * (2 * C * Real.exp (2 * C)) * |b - m| := by
    intro zs
    have hh := abs_cascadeTiltDensity_gaussian_sub_le_of_sup ms vs hmono hpos hle
      (hGlip m) (hGlip b) (mul_nonneg hC.le (abs_nonneg _)) hGdiff x zs
    have hbm : |b - m| ≤ 1 := abs_le.2 ⟨by linarith [hb.1, hm.2], by linarith [hb.2, hm.1]⟩
    change |ρ b zs - ρ m zs| ≤ ρ m zs * Real.exp (2 * (C * |b - m|)) *
      (2 * (C * |b - m|)) at hh
    calc
      _ ≤ ρ m zs * Real.exp (2 * (C * |b - m|)) * (2 * (C * |b - m|)) := hh
      _ ≤ ρ m zs * Real.exp (2 * C) * (2 * (C * |b - m|)) := by
        gcongr
        nlinarith
      _ = _ := by ring
  have hI : ∀ c ∈ Icc (0 : ℝ) 1,
      Integrable (fun zs => ρ c zs * coleHopfMassDeriv c v A (x + ∑ i, zs i)) μ := by
    intro c hc
    have hDm : Measurable (fun zs : Fin j → ℝ => coleHopfMassDeriv c v A (x + ∑ i, zs i)) :=
      ((continuous_coleHopfMassDeriv
        (lipschitzWith_toNNReal_of_abs_sub_le hLip').continuous hAg c v).measurable.comp
        (measurable_const.add (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)))
    have hh := (hρ c).bdd_mul hDm.aestronglyMeasurable
      (.of_forall fun zs => by simpa only [Real.norm_eq_abs] using hD c hc (x + ∑ i, zs i))
    exact hh.congr (.of_forall fun zs => mul_comm _ _)
  have hInt : ∀ c, coleHopfIterateMassDeriv ms vs v A c x =
      ∫ zs, ρ c zs * coleHopfMassDeriv c v A (x + ∑ i, zs i) ∂μ := by
    intro c
    exact integral_cascadeTiltMeasure j ms _ (hGm c) (hGp c) hpos hle (hGfin c) _
  rw [hInt b, hInt m, ← integral_sub (hI b hb) (hI m hm), ← Real.norm_eq_abs]
  have hbound := norm_integral_le_of_norm_le
    (f := fun zs => ρ b zs * coleHopfMassDeriv b v A (x + ∑ i, zs i) -
      ρ m zs * coleHopfMassDeriv m v A (x + ∑ i, zs i))
    (((hρ b).const_mul (L * |b - m|)).add
      ((hρ m).const_mul (2 * C ^ 2 * Real.exp (2 * C) * |b - m|)))
    (.of_forall fun zs => ?_)
  · refine hbound.trans_eq ?_
    simp only [Pi.add_apply]
    rw [integral_add ((hρ b).const_mul _) ((hρ m).const_mul _),
      integral_const_mul, integral_const_mul, hρint b, hρint m]
    dsimp only [M]
    ring
  · simp only [Pi.add_apply, Real.norm_eq_abs]
    have hρb : 0 ≤ ρ b zs := ENNReal.toReal_nonneg
    have hρm : 0 ≤ ρ m zs := ENNReal.toReal_nonneg
    have heq : ρ b zs * coleHopfMassDeriv b v A (x + ∑ i, zs i) -
        ρ m zs * coleHopfMassDeriv m v A (x + ∑ i, zs i) =
        (coleHopfMassDeriv b v A (x + ∑ i, zs i) -
          coleHopfMassDeriv m v A (x + ∑ i, zs i)) * ρ b zs +
        coleHopfMassDeriv m v A (x + ∑ i, zs i) * (ρ b zs - ρ m zs) := by ring
    rw [heq]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hρb]
    have h1 := mul_le_mul_of_nonneg_right (hDdiff (x + ∑ i, zs i)) hρb
    have h2 := mul_le_mul (hD m hm (x + ∑ i, zs i)) (hρdiff zs) (abs_nonneg _) hC.le
    nlinarith

/-- The full ordered prefix has a quadratic mass remainder whose coefficient
depends only on the variance ceiling. Zero varied mass is included. -/
theorem exists_uniform_coleHopfIterate_mass_taylor_bound (V : ℝ≥0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (j : ℕ) (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0),
      Monotone ms → (∀ i, 0 < ms i) → (∀ i, ms i ≤ 1) →
      ∀ (A : ℝ → ℝ), Measurable A → (∀ x y, |A y - A x| ≤ |y - x|) →
      ∀ (v : ℝ≥0), v ≤ V → ∀ x, ∀ m ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        |coleHopfIterate j ms vs (coleHopf b v A) x -
          coleHopfIterate j ms vs (coleHopf m v A) x -
          coleHopfIterateMassDeriv ms vs v A m x * (b - m)| ≤ M * (b - m) ^ 2 := by
  obtain ⟨M, hM, hLipD⟩ := exists_uniform_coleHopfIterateMassDeriv_lipschitz_bound V
  refine ⟨M / 2, by positivity, ?_⟩
  intro j ms vs hmono hpos hle A hAm hLip v hv x m hm b hb
  have hd : ∀ c ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t => coleHopfIterate j ms vs (coleHopf t v A) x)
        (coleHopfIterateMassDeriv ms vs v A c x) c :=
    fun c hc => hasDerivAt_coleHopfIterate_mass_layer ms vs hpos hle hAm hLip v hc x
  exact Aristotle.abs_taylor_one_le zero_le_one hM.le
    (fun c hc => (hd c hc).continuousAt.continuousWithinAt)
    (fun c hc => hd c (Ioo_subset_Icc_self hc))
    (hLipD j ms vs hmono hpos hle A hAm hLip v hv x) hm hb

/-- The propagated Taylor coefficient also works after averaging over any
probability law with an integrable spatial shift. In the Parisi application
the shift is the site field plus its independent root Gaussian. -/
theorem exists_uniform_integral_coleHopfIterate_mass_taylor_bound (V : ℝ≥0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (j : ℕ) (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0),
      Monotone ms → (∀ i, 0 < ms i) → (∀ i, ms i ≤ 1) →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      {H : Ω → ℝ}, Measurable H → Integrable H μ →
      ∀ (A : ℝ → ℝ), Measurable A → (∀ x y, |A y - A x| ≤ |y - x|) →
      ∀ (v : ℝ≥0), v ≤ V → ∀ m ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        |(∫ ω, coleHopfIterate j ms vs (coleHopf b v A) (H ω) ∂μ) -
          (∫ ω, coleHopfIterate j ms vs (coleHopf m v A) (H ω) ∂μ) -
          (∫ ω, coleHopfIterateMassDeriv ms vs v A m (H ω) ∂μ) * (b - m)| ≤
          M * (b - m) ^ 2 := by
  obtain ⟨M, hM, hLipD⟩ := exists_uniform_coleHopfIterateMassDeriv_lipschitz_bound V
  obtain ⟨C, _, hD⟩ := exists_uniform_coleHopfIterate_mass_derivative_bound V
  refine ⟨M / 2, by positivity, ?_⟩
  intro j ms vs hmono hpos hle Ω _ μ _ H hHm hH A hAm hLip v hv m hm b hb
  have hDi : ∀ c ∈ Icc (0 : ℝ) 1,
      Integrable (fun ω => coleHopfIterateMassDeriv ms vs v A c (H ω)) μ := by
    intro c hc
    refine Integrable.of_bound
      ((measurable_coleHopfIterateMassDeriv ms vs hpos hle hAm hLip v hc).comp
        hHm).aestronglyMeasurable C (.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact hD j ms vs hpos hle A hAm hLip v hv c hc (H ω)
  let D : ℝ → ℝ := fun c => ∫ ω, coleHopfIterateMassDeriv ms vs v A c (H ω) ∂μ
  have hd : ∀ c ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t => ∫ ω, coleHopfIterate j ms vs (coleHopf t v A) (H ω) ∂μ)
        (D c) c := by
    intro c hc
    simpa only [add_zero] using hasDerivAt_integral_coleHopfIterate_mass_layer_comp
      hHm hH ms vs hpos hle hAm hLip v 0 hc
  have hDLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |D s - D t| ≤ M * |s - t| := by
    intro s hs t ht
    have hh := norm_integral_le_of_norm_le_const (μ := μ) (C := M * |s - t|)
      (f := fun ω => coleHopfIterateMassDeriv ms vs v A s (H ω) -
        coleHopfIterateMassDeriv ms vs v A t (H ω))
      (.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using
          hLipD j ms vs hmono hpos hle A hAm hLip v hv (H ω) s hs t ht)
    rw [integral_sub (hDi s hs) (hDi t ht)] at hh
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hh
  exact Aristotle.abs_taylor_one_le zero_le_one hM.le
    (fun c hc => (hd c hc).continuousAt.continuousWithinAt)
    (fun c hc => hd c (Ioo_subset_Icc_self hc)) hDLip hm hb

end SpinGlass
