import SpinGlass.Parisi.Variational.ParisiSpatialBounds
import SpinGlass.Parisi.Variational.ParisiMassPropagation

/-!
# Uniform third spatial derivatives

The ordered masses telescope in the first two spatial derivatives of the
actual Gaussian cascade log density. The resulting bounds are independent
of the number of levels. Differentiating the transported terminal gradient
twice then gives a uniform version of the input needed from (14.272).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- The spatial derivative family of the actual cascade log density. -/
noncomputable def coleHopfIterateTiltSpatialJet (i : ℕ) : (j : ℕ) →
    (Fin j → ℝ) → (Fin j → ℝ≥0) → (ℝ → ℝ) → ℝ → (Fin j → ℝ) → ℝ
  | 0, _, _, _, _, _ => 0
  | j + 1, ms, vs, A, x, zs =>
      ms 0 * (iteratedDeriv i (coleHopfIterate j (Fin.tail ms) (Fin.tail vs) A)
        (x + zs 0) - iteratedDeriv i (coleHopfIterate (j + 1) ms vs A) x) +
      coleHopfIterateTiltSpatialJet i j (Fin.tail ms) (Fin.tail vs) A
        (x + zs 0) (Fin.tail zs)

theorem coleHopfIterateTiltSpatialJet_zero {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (A : ℝ → ℝ) (x : ℝ) (zs : Fin j → ℝ) :
    coleHopfIterateTiltSpatialJet 0 j ms vs A x zs =
      coleHopfIterateTiltLog j ms vs A x zs := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
      simp only [coleHopfIterateTiltSpatialJet, iteratedDeriv_zero,
        coleHopfIterateTiltLog, ih]

/-- The family consists of actual spatial derivatives, rather than formal jets. -/
theorem hasDerivAt_coleHopfIterateTiltSpatialJet {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ i ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv i A x| ≤ C)
    {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) {i : ℕ} (hi : i < 4)
    (x : ℝ) (zs : Fin j → ℝ) :
    HasDerivAt (fun y => coleHopfIterateTiltSpatialJet i j ms vs A y zs)
      (coleHopfIterateTiltSpatialJet (i + 1) j ms vs A x zs) x := by
  induction j generalizing x with
  | zero => exact hasDerivAt_const x 0
  | succ j ih =>
      have hB := (coleHopfIterate_spatial_regular_four ms vs hA hb).1
      have hT := (coleHopfIterate_spatial_regular_four (Fin.tail ms) (Fin.tail vs) hA hb).1
      have hdB : HasDerivAt (iteratedDeriv i (coleHopfIterate (j + 1) ms vs A))
          (iteratedDeriv (i + 1) (coleHopfIterate (j + 1) ms vs A) x) x := by
        rw [iteratedDeriv_succ]
        exact ((hB.differentiable_iteratedDeriv i (by exact_mod_cast hi)) x).hasDerivAt
      have hdT : HasDerivAt
          (iteratedDeriv i (coleHopfIterate j (Fin.tail ms) (Fin.tail vs) A))
          (iteratedDeriv (i + 1) (coleHopfIterate j (Fin.tail ms) (Fin.tail vs) A)
            (x + zs 0)) (x + zs 0) := by
        rw [iteratedDeriv_succ]
        exact ((hT.differentiable_iteratedDeriv i (by exact_mod_cast hi)) _).hasDerivAt
      convert!
        (((hdT.comp x ((hasDerivAt_id x).add_const (zs 0))).sub hdB).const_mul
        (ms 0) |>.add (ih (Fin.tail ms) (Fin.tail vs) (x + zs 0) (Fin.tail zs) |>.comp x
          ((hasDerivAt_id x).add_const (zs 0)))) using 1
      simp only [coleHopfIterateTiltSpatialJet, mul_one]

/-- Spatial jets depend continuously on position and Gaussian marks. -/
theorem continuous_coleHopfIterateTiltSpatialJet {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ i ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv i A x| ≤ C)
    {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) {i : ℕ} (hi : i ≤ 4) :
    Continuous (fun q : ℝ × (Fin j → ℝ) =>
      coleHopfIterateTiltSpatialJet i j ms vs A q.1 q.2) := by
  induction j with
  | zero => exact continuous_const
  | succ j ih =>
      have hT := (coleHopfIterate_spatial_regular_four (Fin.tail ms) (Fin.tail vs) hA hb).1
      have hB := (coleHopfIterate_spatial_regular_four ms vs hA hb).1
      have hshift : Continuous (fun q : ℝ × (Fin (j + 1) → ℝ) => q.1 + q.2 0) :=
        continuous_fst.add ((continuous_apply 0).comp continuous_snd)
      have htail : Continuous (fun q : ℝ × (Fin (j + 1) → ℝ) => Fin.tail q.2) :=
        continuous_pi fun p => (continuous_apply p.succ).comp continuous_snd
      exact (continuous_const.mul
        (((hT.continuous_iteratedDeriv i (by exact_mod_cast hi)).comp hshift).sub
          ((hB.continuous_iteratedDeriv i (by exact_mod_cast hi)).comp continuous_fst))).add
        ((ih (Fin.tail ms) (Fin.tail vs)).comp (hshift.prodMk htail))

/-- Each fixed-position jet is measurable in the Gaussian marks. -/
theorem measurable_coleHopfIterateTiltSpatialJet {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ i ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv i A x| ≤ C)
    {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) {i : ℕ} (hi : i ≤ 4) (x : ℝ) :
    Measurable (fun zs => coleHopfIterateTiltSpatialJet i j ms vs A x zs) :=
  ((continuous_coleHopfIterateTiltSpatialJet hA hb ms vs hi).comp
    (continuous_const.prodMk continuous_id)).measurable

private theorem abs_tiltSpatialJet_add_le {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ i ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv i A x| ≤ C)
    (hsharp : ∀ x, 0 ≤ deriv (deriv A) x ∧ deriv (deriv A) x + deriv A x ^ 2 ≤ 1)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 2) (j : ℕ) :
    ∀ (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0), Monotone ms →
      (∀ p, ms p ≤ 1) → ∀ a : ℝ, 0 ≤ a → a ≤ 1 → (∀ p, a ≤ ms p) → ∀ x zs,
      |coleHopfIterateTiltSpatialJet i j ms vs A x zs +
        a * iteratedDeriv i (coleHopfIterate j ms vs A) x| ≤ 2 - a := by
  have hbound : ∀ {n : ℕ} (ns : Fin n → ℝ) (ws : Fin n → ℝ≥0),
      (∀ p, ns p ∈ Icc (0 : ℝ) 1) → ∀ y,
      |iteratedDeriv i (coleHopfIterate n ns ws A) y| ≤ 1 := by
    intro n ns ws hn y
    have hs := coleHopfIterate_sharp_spatial_bounds hA hb hsharp ns ws hn y
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
    interval_cases i
    · rw [iteratedDeriv_one]
      apply abs_le.2
      constructor <;> nlinarith [hs.1, hs.2]
    · simp only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
      rw [abs_of_nonneg hs.1]
      nlinarith [hs.2, sq_nonneg (deriv (coleHopfIterate n ns ws A) y)]
  induction j with
  | zero =>
      intro ms vs hmono hle a ha ha1 hal x zs
      simp only [coleHopfIterateTiltSpatialJet, zero_add]
      rw [abs_mul, abs_of_nonneg ha]
      exact (mul_le_mul_of_nonneg_left (hbound ms vs (fun p => Fin.elim0 p) x) ha).trans
        (by linarith)
  | succ j ih =>
      intro ms vs hmono hle a ha ha1 hal x zs
      have hm : ∀ p, ms p ∈ Icc (0 : ℝ) 1 := fun p => ⟨ha.trans (hal p), hle p⟩
      have ht := ih (Fin.tail ms) (Fin.tail vs)
        (fun p q hpq => hmono (Fin.succ_le_succ_iff.2 hpq))
        (fun p => hle p.succ) (ms 0) (hm 0).1 (hm 0).2
        (fun p => hmono (Fin.zero_le _)) (x + zs 0) (Fin.tail zs)
      have hr : |(ms 0 - a) * iteratedDeriv i (coleHopfIterate (j + 1) ms vs A) x| ≤
          ms 0 - a := by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (hal 0))]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (hbound ms vs hm x) (sub_nonneg.2 (hal 0))
      have heq : coleHopfIterateTiltSpatialJet i (j + 1) ms vs A x zs +
          a * iteratedDeriv i (coleHopfIterate (j + 1) ms vs A) x =
          (coleHopfIterateTiltSpatialJet i j (Fin.tail ms) (Fin.tail vs) A
            (x + zs 0) (Fin.tail zs) + ms 0 *
              iteratedDeriv i (coleHopfIterate j (Fin.tail ms) (Fin.tail vs) A) (x + zs 0)) -
          (ms 0 - a) * iteratedDeriv i (coleHopfIterate (j + 1) ms vs A) x := by
        simp only [coleHopfIterateTiltSpatialJet]
        ring
      rw [heq]
      exact (abs_sub _ _).trans ((add_le_add ht hr).trans_eq (by ring))

/-- Ordered masses give spatial log-density derivatives bounded by two.
This is uniform in the number of levels and all Gaussian variances. -/
theorem abs_coleHopfIterateTiltSpatialJet_le_two {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ i ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv i A x| ≤ C)
    (hsharp : ∀ x, 0 ≤ deriv (deriv A) x ∧ deriv (deriv A) x + deriv A x ^ 2 ≤ 1)
    {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (hmono : Monotone ms)
    (hm : ∀ p, ms p ∈ Icc (0 : ℝ) 1) {i : ℕ} (hi : i ∈ Finset.Icc 1 2)
    (x : ℝ) (zs : Fin j → ℝ) :
    |coleHopfIterateTiltSpatialJet i j ms vs A x zs| ≤ 2 := by
  simpa only [zero_mul, add_zero, sub_zero] using
    abs_tiltSpatialJet_add_le hA hb hsharp hi j ms vs hmono (fun p => (hm p).2)
      0 le_rfl zero_le_one (fun p => (hm p).1) x zs

private theorem iterate_gradient_eq_integral_density {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hLip : ∀ x y, |A y - A x| ≤ 1 * |y - x|)
    (hfirst : ∀ x, |deriv A x| ≤ 1)
    {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1) (x : ℝ) :
    deriv (coleHopfIterate j ms vs A) x =
      ∫ zs, deriv A (x + ∑ p, zs p) * Real.exp
        (coleHopfIterateTiltSpatialJet 0 j ms vs A x zs)
        ∂Measure.pi (fun p => gaussianReal 0 (vs p)) := by
  have hAd := hA.differentiable (by norm_num)
  have hA₁c := hA.continuous_deriv (by norm_num)
  have hd := hasDerivAt_coleHopfIterate ms vs hpos hle
    (G := fun l y => A (l + y)) (G' := fun l y => deriv A (l + y))
    (fun l => hA₁c.measurable.comp (measurable_const.add measurable_id))
    (fun l y => by
      convert! (hAd (l + y)).hasDerivAt.comp l ((hasDerivAt_id l).add_const y) using 1
      simp only [mul_one])
    (fun l y => hfirst (l + y))
    (fun l y z => by simpa only [add_sub_add_left_eq_sub] using hLip (l + y) (l + z)) x 0
  have heq : (fun l => coleHopfIterate j ms vs (fun y => A (l + y)) 0) =
      coleHopfIterate j ms vs A := by
    funext l
    rw [coleHopfIterate_translate, add_zero]
  rw [heq] at hd
  rw [hd.deriv]
  simp only [zero_add]
  have hGm : Measurable (fun zs : Fin j → ℝ =>
      ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (hA.continuous.measurable.comp
        (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))))
  rw [integral_cascadeTiltMeasure j ms _ hGm
    (fun zs => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos hle
    (lintegral_ofReal_exp_comp_add_sum_pi_gaussianReal_ne_top vs hLip x)]
  apply integral_congr_ae
  exact .of_forall fun zs => by
    simp only [smul_eq_mul, coleHopfIterateTiltSpatialJet_zero,
      cascadeTiltDensity_gaussian_eq_exp_tiltLog j ms vs hpos hLip, mul_comm]

/-- A uniform third spatial derivative bound for ordered positive masses.
The constant is the terminal third-derivative bound plus ten, with no level
count or variance dependence. It is a sufficient bound for the Taylor use
of Talagrand, Vol. II, (14.272), rather than its sharper coefficient four. -/
theorem coleHopfIterate_third_spatial_bound {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A) {C C₃ : ℝ}
    (hb : ∀ i ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv i A x| ≤ C)
    (hsharp : ∀ x, 0 ≤ deriv (deriv A) x ∧ deriv (deriv A) x + deriv A x ^ 2 ≤ 1)
    (hthird : ∀ x, |iteratedDeriv 3 A x| ≤ C₃)
    {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hmono : Monotone ms) (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1) (x : ℝ) :
    |iteratedDeriv 3 (coleHopfIterate j ms vs A) x| ≤ C₃ + 10 := by
  let μ := Measure.pi (fun p => gaussianReal 0 (vs p))
  let L := fun i y zs => coleHopfIterateTiltSpatialJet i j ms vs A y zs
  let ρ := fun y zs => Real.exp (L 0 y zs)
  let D : ℕ → ℝ → (Fin j → ℝ) → ℝ := fun i y zs => iteratedDeriv i A (y + ∑ p, zs p)
  let F₀ := fun y zs => D 1 y zs * ρ y zs
  let F₁ := fun y zs => (D 2 y zs + D 1 y zs * L 1 y zs) * ρ y zs
  let F₂ := fun y zs => (D 3 y zs + 2 * D 2 y zs * L 1 y zs +
    D 1 y zs * (L 2 y zs + L 1 y zs ^ 2)) * ρ y zs
  have hfirst : ∀ y, |deriv A y| ≤ 1 := fun y => by
    apply abs_le.2
    constructor <;> nlinarith [(hsharp y).1, (hsharp y).2]
  have hsecond : ∀ y, |deriv (deriv A) y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (hsharp y).1]
    nlinarith [(hsharp y).2, sq_nonneg (deriv A y)]
  have hD₁ : ∀ y zs, |D 1 y zs| ≤ 1 := by
    intro y zs
    simpa only [D, iteratedDeriv_one] using hfirst (y + ∑ p, zs p)
  have hD₂ : ∀ y zs, |D 2 y zs| ≤ 1 := by
    intro y zs
    simpa only [D, show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_zero] using hsecond (y + ∑ p, zs p)
  have hD₃ : ∀ y zs, |D 3 y zs| ≤ C₃ := fun y zs => hthird _
  have hC₃ : 0 ≤ C₃ := (abs_nonneg _).trans (hthird 0)
  have hAd := hA.differentiable (by norm_num)
  have hLip : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    intro y z
    simpa only [Real.norm_eq_abs] using
      (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun y _ => hAd y)
        (fun y _ => by simpa only [Real.norm_eq_abs] using hfirst y)
        (mem_univ y) (mem_univ z)
  have hLbound : ∀ i ∈ Finset.Icc 1 2, ∀ y zs, |L i y zs| ≤ 2 := fun i hi y zs =>
    abs_coleHopfIterateTiltSpatialJet_le_two hA hb hsharp ms vs hmono
      (fun p => ⟨(hpos p).le, hle p⟩) hi y zs
  have hLd : ∀ i < 4, ∀ y zs, HasDerivAt (fun t => L i t zs) (L (i + 1) y zs) y :=
    fun i hi y zs => hasDerivAt_coleHopfIterateTiltSpatialJet hA ⟨C, hb⟩ ms vs hi y zs
  have hDd : ∀ i < 4, ∀ y zs, HasDerivAt (fun t => D i t zs) (D (i + 1) y zs) y := by
    intro i hi y zs
    have hd : HasDerivAt (iteratedDeriv i A) (iteratedDeriv (i + 1) A
        (y + ∑ p, zs p)) (y + ∑ p, zs p) := by
      rw [iteratedDeriv_succ]
      exact ((hA.differentiable_iteratedDeriv i (by exact_mod_cast hi)) _).hasDerivAt
    convert! hd.comp y ((hasDerivAt_id y).add_const (∑ p, zs p)) using 1
    simp only [D, mul_one]
  have hρd : ∀ y zs, HasDerivAt (fun t => ρ t zs) (L 1 y zs * ρ y zs) y := by
    intro y zs
    convert! (hLd 0 (by norm_num) y zs).exp using 1
    simp only [ρ]
    ring
  have hF₀d : ∀ y zs, HasDerivAt (fun t => F₀ t zs) (F₁ y zs) y := by
    intro y zs
    convert! (hDd 1 (by norm_num) y zs).mul (hρd y zs) using 1
    simp only [F₁]
    ring
  have hF₁d : ∀ y zs, HasDerivAt (fun t => F₁ t zs) (F₂ y zs) y := by
    intro y zs
    convert! ((hDd 2 (by norm_num) y zs).add
      ((hDd 1 (by norm_num) y zs).mul (hLd 1 (by norm_num) y zs))).mul
        (hρd y zs) using 1
    simp only [F₂, Pi.add_apply, Pi.mul_apply]
    ring
  have hDm : ∀ i ≤ 4, ∀ y, Measurable (D i y) := fun i hi y =>
    (hA.continuous_iteratedDeriv i (by exact_mod_cast hi)).measurable.comp
      (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))
  have hLm : ∀ i ≤ 4, ∀ y, Measurable (L i y) := fun i hi y =>
    measurable_coleHopfIterateTiltSpatialJet hA ⟨C, hb⟩ ms vs hi y
  have hρm : ∀ y, Measurable (ρ y) := fun y => Real.measurable_exp.comp (hLm 0 (by omega) y)
  have hF₀m : ∀ y, Measurable (F₀ y) := fun y => (hDm 1 (by omega) y).mul (hρm y)
  have hF₁m : ∀ y, Measurable (F₁ y) := fun y =>
    ((hDm 2 (by omega) y).add ((hDm 1 (by omega) y).mul
      (hLm 1 (by omega) y))).mul (hρm y)
  have hF₂m : ∀ y, Measurable (F₂ y) := fun y =>
    (((hDm 3 (by omega) y).add (measurable_const.mul (hDm 2 (by omega) y) |>.mul
      (hLm 1 (by omega) y))).add ((hDm 1 (by omega) y).mul
        ((hLm 2 (by omega) y).add ((hLm 1 (by omega) y).pow_const 2)))).mul (hρm y)
  have hρi : Integrable (ρ x) μ := by
    have hGm : Measurable (fun zs : Fin j → ℝ =>
        ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p)))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (hA.continuous.measurable.comp
          (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))))
    have hi := integrable_toReal_cascadeTiltDensity j ms _ hGm
      (fun zs => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos hle
      (lintegral_ofReal_exp_comp_add_sum_pi_gaussianReal_ne_top vs hLip x)
    simpa only [ρ, L, coleHopfIterateTiltSpatialJet_zero,
      cascadeTiltDensity_gaussian_eq_exp_tiltLog j ms vs hpos hLip] using hi
  have hρint : ∫ zs, ρ x zs ∂μ = 1 := by
    have hGm : Measurable (fun zs : Fin j → ℝ =>
        ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p)))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (hA.continuous.measurable.comp
          (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))))
    have hGpos := fun zs : Fin j → ℝ => ENNReal.ofReal_pos.2 (Real.exp_pos
      (A (x + ∑ p, zs p)))
    have hGfin := lintegral_ofReal_exp_comp_add_sum_pi_gaussianReal_ne_top vs hLip x
    have := isProbabilityMeasure_cascadeTiltMeasure j ms _ hGm hGpos hpos hle hGfin
    have heq := integral_cascadeTiltMeasure j ms _ hGm hGpos hpos hle hGfin
      (fun _ => (1 : ℝ))
    simpa only [μ, ρ, L, coleHopfIterateTiltSpatialJet_zero, smul_eq_mul, mul_one,
      cascadeTiltDensity_gaussian_eq_exp_tiltLog j ms vs hpos hLip,
      integral_const, probReal_univ, one_smul] using heq.symm
  have hF₁bound : ∀ y zs, |F₁ y zs| ≤ 3 * ρ y zs := by
    intro y zs
    dsimp only [F₁]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc
      _ ≤ |D 2 y zs| + |D 1 y zs| * |L 1 y zs| := by rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 + 1 * 2 := add_le_add (hD₂ y zs)
        (mul_le_mul (hD₁ y zs) (hLbound 1 (by decide) y zs) (abs_nonneg _) zero_le_one)
      _ = 3 := by norm_num
  have hF₂bound : ∀ y zs, |F₂ y zs| ≤ (C₃ + 10) * ρ y zs := by
    intro y zs
    have hL₁ := hLbound 1 (by decide) y zs
    have hL₂ := hLbound 2 (by decide) y zs
    have ht₁ : |2 * D 2 y zs * L 1 y zs| ≤ 4 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hh := mul_le_mul (hD₂ y zs) hL₁ (abs_nonneg _) zero_le_one
      nlinarith
    have ht₂a : |L 2 y zs + L 1 y zs ^ 2| ≤ 6 := by
      have hh : |L 1 y zs ^ 2| ≤ 4 := by
        rw [abs_pow]
        simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
          pow_le_pow_left₀ (abs_nonneg _) hL₁ 2
      exact (abs_add_le _ _).trans (by linarith)
    have ht₂ : |D 1 y zs * (L 2 y zs + L 1 y zs ^ 2)| ≤ 6 := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul (hD₁ y zs) ht₂a (abs_nonneg _) zero_le_one
    dsimp only [F₂]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc
      _ ≤ |D 3 y zs| + |2 * D 2 y zs * L 1 y zs| +
          |D 1 y zs * (L 2 y zs + L 1 y zs ^ 2)| := (abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ C₃ + 4 + 6 := add_le_add (add_le_add (hD₃ y zs) ht₁) ht₂
      _ = C₃ + 10 := by ring
  have hρlocal : ∀ zs y, |y - x| < 1 → ρ y zs ≤ Real.exp 2 * ρ x zs := by
    intro zs y hy
    have hdiff : |L 0 y zs - L 0 x zs| ≤ 2 * |y - x| := by
      simpa only [Real.norm_eq_abs] using
        (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
          (fun t _ => (hLd 0 (by omega) t zs).differentiableAt)
          (fun t _ => by
            rw [(hLd 0 (by omega) t zs).deriv, Real.norm_eq_abs]
            exact hLbound 1 (by decide) t zs) (mem_univ x) (mem_univ y)
    dsimp only [ρ]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith [le_abs_self (L 0 y zs - L 0 x zs)]
  have hF₁i : Integrable (F₁ x) μ :=
    (hρi.const_mul 3).mono' (hF₁m x).aestronglyMeasurable
      (.of_forall fun zs => by rw [Real.norm_eq_abs]; exact hF₁bound x zs)
  have hd₀ : ∀ y, HasDerivAt (fun t => ∫ zs, F₀ t zs ∂μ) (∫ zs, F₁ y zs ∂μ) y := by
    intro y
    -- Domination is relative to the fixed density at y.
    have hyi : Integrable (ρ y) μ := by
      have hdiff : ∀ zs, ρ y zs ≤ Real.exp (2 * |y - x|) * ρ x zs := by
        intro zs
        have hh := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
          (fun t _ => (hLd 0 (by omega) t zs).differentiableAt)
          (fun t _ => by
            rw [(hLd 0 (by omega) t zs).deriv, Real.norm_eq_abs]
            exact hLbound 1 (by decide) t zs) (mem_univ x) (mem_univ y)
        simp only [Real.norm_eq_abs] at hh
        dsimp only [ρ]
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        linarith [le_abs_self (L 0 y zs - L 0 x zs)]
      exact (hρi.const_mul _).mono' (hρm y).aestronglyMeasurable
        (.of_forall fun zs => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hdiff zs)
    have hyF : Integrable (F₀ y) μ :=
      (hyi.bdd_mul (hDm 1 (by omega) y).aestronglyMeasurable
        (.of_forall fun zs => by simpa only [Real.norm_eq_abs] using hD₁ y zs)).congr
          (.of_forall fun zs => rfl)
    have hylocal : ∀ zs t, |t - y| < 1 → ρ t zs ≤ Real.exp 2 * ρ y zs := by
      intro zs t ht
      have hh := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun s _ => (hLd 0 (by omega) s zs).differentiableAt)
        (fun s _ => by
          rw [(hLd 0 (by omega) s zs).deriv, Real.norm_eq_abs]
          exact hLbound 1 (by decide) s zs) (mem_univ y) (mem_univ t)
      simp only [Real.norm_eq_abs] at hh
      dsimp only [ρ]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      linarith [le_abs_self (L 0 t zs - L 0 y zs)]
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds y (by norm_num : (0 : ℝ) < 1))
      (.of_forall fun t => (hF₀m t).aestronglyMeasurable) hyF
      (hF₁m y).aestronglyMeasurable
      (.of_forall fun zs t ht => by
        rw [Real.norm_eq_abs]
        exact (hF₁bound t zs).trans (mul_le_mul_of_nonneg_left
          (hylocal zs t (by simpa only [Metric.mem_ball, Real.dist_eq] using ht))
            (by norm_num)))
      ((hyi.const_mul (Real.exp 2)).const_mul 3)
      (.of_forall fun zs t _ => hF₀d t zs)).2
  have hd₁ := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1))
    (.of_forall fun t => (hF₁m t).aestronglyMeasurable) hF₁i
    (hF₂m x).aestronglyMeasurable
    (.of_forall fun zs t ht => by
      rw [Real.norm_eq_abs]
      exact (hF₂bound t zs).trans (mul_le_mul_of_nonneg_left
        (hρlocal zs t (by simpa only [Metric.mem_ball, Real.dist_eq] using ht))
          (by positivity)))
    ((hρi.const_mul (Real.exp 2)).const_mul (C₃ + 10))
    (.of_forall fun zs t _ => hF₁d t zs)).2
  have heq₀ : deriv (coleHopfIterate j ms vs A) = fun t => ∫ zs, F₀ t zs ∂μ := by
    funext t
    simpa only [F₀, D, ρ, L, iteratedDeriv_one] using
      iterate_gradient_eq_integral_density hA hLip hfirst ms vs hpos hle t
  have heq₁ : deriv (deriv (coleHopfIterate j ms vs A)) =
      fun t => ∫ zs, F₁ t zs ∂μ := by
    rw [heq₀]
    exact funext fun t => (hd₀ t).deriv
  have heq₂ : iteratedDeriv 3 (coleHopfIterate j ms vs A) x = ∫ zs, F₂ x zs ∂μ := by
    simp only [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
    rw [heq₁, hd₁.deriv]
  rw [heq₂, ← Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le ((hρi.const_mul (C₃ + 10)))
    (.of_forall fun zs => by rw [Real.norm_eq_abs]; exact hF₂bound x zs)
  exact hh.trans_eq (by rw [integral_const_mul, hρint, mul_one])

/-- The extended masses remain ordered across both fixed endpoints. -/
theorem ParisiMAdmissible.monotone_mExt {k : ℕ} {ms : Fin k → ℝ}
    (hm : ParisiMAdmissible ms) : Monotone (mExt ms) := by
  intro p q hpq
  rcases p with _ | p
  · rw [mExt_zero]
    rcases q with _ | q
    · rw [mExt_zero]
    · exact (hm.mExt_pos (by omega)).le
  · rcases q with _ | q
    · omega
    · by_cases hq : q < k
      · have hp : p < k := by omega
        rw [show p + 1 = (⟨p, hp⟩ : Fin k).val + 1 by rfl,
          show q + 1 = (⟨q, hq⟩ : Fin k).val + 1 by rfl, mExt_val_succ, mExt_val_succ]
        exact hm.1.monotone (by change p ≤ q; omega)
      · rw [mExt_eq_one_of_le ms (r := q + 1) (by omega)]
        exact mExt_le_one (fun r => (hm.2.2 r).le) _

/-- The actual log-cosh terminal has third derivative bounded by two. -/
theorem parisiLogCoshTerminal_third_spatial_bound (h x : ℝ) :
    |iteratedDeriv 3 (parisiLogCoshTerminal h) x| ≤ 2 := by
  have h₁ : deriv (parisiLogCoshTerminal h) = parisiLogCoshTerminalDeriv h :=
    funext fun y => (hasDerivAt_parisiLogCoshTerminal h y).deriv
  have h₂ : deriv (parisiLogCoshTerminalDeriv h) = parisiLogCoshTerminalDeriv2 h :=
    funext fun y => (hasDerivAt_parisiLogCoshTerminalDeriv h y).deriv
  have hd := (hasDerivAt_const x (1 : ℝ)).sub
    ((hasDerivAt_parisiLogCoshTerminalDeriv h x).pow 2)
  have h₃ : iteratedDeriv 3 (parisiLogCoshTerminal h) x =
      -2 * Real.tanh (h + x) * (1 - Real.tanh (h + x) ^ 2) := by
    simp only [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
    rw [h₁, h₂]
    convert! hd.deriv using 1
    simp only [parisiLogCoshTerminalDeriv, parisiLogCoshTerminalDeriv2]
    ring
  have ht : |Real.tanh (h + x)| ≤ 1 := (Real.abs_tanh_lt_one _).le
  have hs : 0 ≤ 1 - Real.tanh (h + x) ^ 2 := by linarith [Real.tanh_sq_lt_one (h + x)]
  have hs1 : 1 - Real.tanh (h + x) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (Real.tanh (h + x))]
  rw [h₃, abs_mul, abs_mul, abs_of_nonneg hs]
  norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := mul_le_mul ht hs1 hs zero_le_one
  nlinarith

/-- Uniform third spatial derivatives of every actual Parisi suffix.
The numerical coefficient twelve is independent of the field translation,
all parameters and the number of levels. -/
theorem parisiQSuffix_third_spatial_bound (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (x : ℝ) :
    |iteratedDeriv 3 (parisiQSuffix ξ h ms qs r) x| ≤ 12 := by
  obtain ⟨C, hC⟩ := exists_bound_iteratedDeriv_parisiLogCoshTerminal_four h
  simpa only [parisiQSuffix, show (2 : ℝ) + 10 = 12 by norm_num] using
    coleHopfIterate_third_spatial_bound (contDiff_parisiLogCoshTerminal h 4) hC
    (parisiLogCoshTerminal_sharp_spatial_bounds h) (parisiLogCoshTerminal_third_spatial_bound h)
    (parisiQSuffixMasses ms r) (parisiQSuffixVars ξ qs r)
    (fun p q hpq => hm.monotone_mExt (by change r.val + p.val + 2 ≤ r.val + q.val + 2; omega))
    (fun p => hm.mExt_pos (by omega)) (fun p => mExt_le_one (fun s => (hm.2.2 s).le) _) x

/-- A zero-mass layer preserves any third spatial derivative bound.
Its proof uses the expectation branch and includes zero variance. -/
theorem coleHopf_zero_third_spatial_bound {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A) {C C₃ : ℝ}
    (hb : ∀ i ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv i A x| ≤ C)
    (hthird : ∀ x, |iteratedDeriv 3 A x| ≤ C₃) (v : ℝ≥0) (x : ℝ) :
    |iteratedDeriv 3 (coleHopf 0 v A) x| ≤ C₃ := by
  have hJ := Aristotle.Heat.jet_iteratedDeriv hA hb
  have heq := iteratedDeriv_eq_of_derivative_family (n := 4)
    (d := fun i => Aristotle.Heat.heat (v : ℝ) (iteratedDeriv i A))
    (fun i hi y => hJ.heat_hasDerivAt hi (v : ℝ) y)
  rw [coleHopf_eq_gaussianLayer, Aristotle.gaussianLayer_zero_mass]
  change |iteratedDeriv 3 (Aristotle.Heat.heat (v : ℝ) (iteratedDeriv 0 A)) x| ≤ C₃
  rw [heq 3 (by norm_num)]
  have hh := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 v)
    (f := fun z => iteratedDeriv 3 A (x + z))
    (.of_forall fun z => by rw [Real.norm_eq_abs]; exact hthird (x + z))
  simpa only [Aristotle.Heat.heat, Real.toNNReal_coe, Real.norm_eq_abs,
    probReal_univ, mul_one] using hh

/-- Prepending a mass below the ordered log-cosh suffix keeps the same
uniform third-derivative bound. This is the concrete split-layer input to
the overlap Taylor remainder; zero inserted mass is included. -/
theorem coleHopf_ordered_logCoshIterate_third_spatial_bound {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hmono : Monotone ms) (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (hml : ∀ p, m ≤ ms p)
    (v : ℝ≥0) (h x : ℝ) :
    |iteratedDeriv 3 (coleHopf m v
      (coleHopfIterate j ms vs (parisiLogCoshTerminal h))) x| ≤ 12 := by
  obtain ⟨C, hC⟩ := exists_bound_iteratedDeriv_parisiLogCoshTerminal_four h
  rcases eq_or_lt_of_le hm.1 with hm0 | hmpos
  · have hm0' : m = 0 := hm0.symm
    subst m
    obtain ⟨hB, K, hK⟩ := coleHopfIterate_spatial_regular_four ms vs
      (contDiff_parisiLogCoshTerminal h 4) ⟨C, hC⟩
    apply coleHopf_zero_third_spatial_bound hB hK
    intro y
    simpa only [show (2 : ℝ) + 10 = 12 by norm_num] using
      coleHopfIterate_third_spatial_bound (contDiff_parisiLogCoshTerminal h 4) hC
        (parisiLogCoshTerminal_sharp_spatial_bounds h)
        (parisiLogCoshTerminal_third_spatial_bound h) ms vs hmono hpos hle y
  · have hcons : Monotone (Fin.cons (α := fun _ => ℝ) m ms) := by
      intro p
      refine Fin.cases ?_ (fun p => ?_) p
      · intro q
        refine Fin.cases (by simp) (fun q => ?_) q
        intro _
        simpa only [Fin.cons_zero, Fin.cons_succ] using hml q
      · intro q
        refine Fin.cases (by
          intro hpq
          have hh : p.succ.val ≤ (0 : Fin (j + 1)).val := hpq
          simp only [Fin.val_succ, Fin.val_zero] at hh
          omega) (fun q => ?_) q
        intro hpq
        simpa only [Fin.cons_succ] using hmono (Fin.succ_le_succ_iff.1 hpq)
    have hcpos : ∀ p : Fin (j + 1), 0 < Fin.cons (α := fun _ => ℝ) m ms p := by
      intro p
      refine Fin.cases hmpos (fun q => ?_) p
      simpa only [Fin.cons_succ] using hpos q
    have hcle : ∀ p : Fin (j + 1), Fin.cons (α := fun _ => ℝ) m ms p ≤ 1 := by
      intro p
      refine Fin.cases hm.2 (fun q => ?_) p
      simpa only [Fin.cons_succ] using hle q
    have hh := coleHopfIterate_third_spatial_bound
      (contDiff_parisiLogCoshTerminal h 4) hC (parisiLogCoshTerminal_sharp_spatial_bounds h)
      (parisiLogCoshTerminal_third_spatial_bound h)
      (Fin.cons m ms) (Fin.cons v vs) hcons hcpos hcle x
    simpa only [coleHopfIterate_succ, Fin.cons_zero, Fin.tail_cons,
      show (2 : ℝ) + 10 = 12 by norm_num] using hh

/-- The uniform third derivative estimate remains valid after the actual
adjacent overlap layer, including its zero-mass endpoint. -/
theorem coleHopf_parisiQSuffix_third_spatial_bound (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hm : ParisiMAdmissible ms) {m : ℝ} (hm0 : 0 ≤ m)
    (hmr : m ≤ mExt ms (r.val + 2)) (v : ℝ≥0) (x : ℝ) :
    |iteratedDeriv 3 (coleHopf m v (parisiQSuffix ξ h ms qs r)) x| ≤ 12 := by
  apply coleHopf_ordered_logCoshIterate_third_spatial_bound
    (parisiQSuffixMasses ms r) (parisiQSuffixVars ξ qs r)
    (fun p q hpq => hm.monotone_mExt (by change r.val + p.val + 2 ≤ r.val + q.val + 2; omega))
    (fun p => hm.mExt_pos (by omega)) (fun p => mExt_le_one (fun s => (hm.2.2 s).le) _)
    ⟨hm0, hmr.trans (mExt_le_one (fun s => (hm.2.2 s).le) _)⟩
  intro p
  exact hmr.trans (hm.monotone_mExt (by change r.val + 2 ≤ r.val + p.val + 2; omega))

end SpinGlass
