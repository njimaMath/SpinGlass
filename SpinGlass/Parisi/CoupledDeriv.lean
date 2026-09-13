/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.CoupledSite
import SpinGlass.Parisi.CoupledLambdaZero
import Common.Mathlib.Probability.PointProcess.CascadeDeriv
import Common.Mathlib.Probability.PointProcess.CascadePair

/-!
# The `λ`-dependence of `Y₀` (Talagrand Vol. II, §14.6, after Proposition 14.6.3)

The one-site function `Y_{κ+1}(λ) = log (ch A ch B ch λ + sh A sh B sh λ)` of (14.168) has
derivative `pairSiteY'`, bounded by `1` in absolute value (`abs_pairSiteY'_le_one`: with
`T = th λ`, `T₁ = th A`, `T₂ = th B`, `|T + T₁T₂| ≤ 1 + T T₁ T₂`, Talagrand's inequality in the
proof of Lemma 14.6.5). By the derivative of the Parisi recursion in a parameter
(`hasDerivAt_parisiRec`), `Y₁(λ, y₀)` is differentiable in `λ` with derivative the tilted average
of `∂_λ Y_{κ+1}` — Talagrand's (14.185), `Y'_p = 𝔼_p(W_p Y'_{p+1})`, iterated
(`hasDerivAt_parisiRec_pairSiteF`) — and so is `Y₀(λ) = 𝔼 Y₁(λ, y₀)`
(`hasDerivAt_pairSiteY₀`), with `|Y₀'(λ)| ≤ 1` (`abs_pairSiteY₀'_le_one`).
-/

open MeasureTheory ProbabilityTheory Finset Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

/-! ### The derivative of `Y_{κ+1}` in `λ` -/

/-- `∂_λ Y_{κ+1} = (ch A ch B sh λ + sh A sh B ch λ) / (ch A ch B ch λ + sh A sh B sh λ)`. -/
def pairSiteY' (lam A B : ℝ) : ℝ :=
  (Real.cosh A * Real.cosh B * Real.sinh lam + Real.sinh A * Real.sinh B * Real.cosh lam)
    / (Real.cosh A * Real.cosh B * Real.cosh lam + Real.sinh A * Real.sinh B * Real.sinh lam)

lemma hasDerivAt_pairSiteY (A B lam : ℝ) :
    HasDerivAt (fun l => pairSiteY l A B) (pairSiteY' lam A B) lam := by
  unfold pairSiteY pairSiteY'
  have h1 : HasDerivAt (fun l => Real.cosh A * Real.cosh B * Real.cosh l
      + Real.sinh A * Real.sinh B * Real.sinh l)
      (Real.cosh A * Real.cosh B * Real.sinh lam + Real.sinh A * Real.sinh B * Real.cosh lam)
      lam :=
    ((Real.hasDerivAt_cosh lam).const_mul _).add ((Real.hasDerivAt_sinh lam).const_mul _)
  exact h1.log (cosh_mul_cosh_mul_cosh_add_sinh_mul_sinh_mul_sinh_pos A B lam).ne'

/-- **Talagrand's inequality** (proof of Lemma 14.6.5):
`|ch A ch B sh λ + sh A sh B ch λ| ≤ ch A ch B ch λ + sh A sh B sh λ`, i.e. `|∂_λ Y_{κ+1}| ≤ 1`. -/
lemma abs_pairSiteY'_le_one (lam A B : ℝ) : |pairSiteY' lam A B| ≤ 1 := by
  unfold pairSiteY'
  have hc := cosh_mul_cosh_mul_cosh_add_sinh_mul_sinh_mul_sinh_pos A B lam
  rw [abs_div, abs_of_pos hc, div_le_one hc, abs_le]
  have h1 : Real.cosh A * Real.cosh B * Real.cosh lam + Real.sinh A * Real.sinh B * Real.sinh lam
      + (Real.cosh A * Real.cosh B * Real.sinh lam + Real.sinh A * Real.sinh B * Real.cosh lam)
      = Real.exp lam * Real.cosh (A + B) := by
    rw [Real.cosh_add, ← Real.cosh_add_sinh]
    ring
  have h2 : Real.cosh A * Real.cosh B * Real.cosh lam + Real.sinh A * Real.sinh B * Real.sinh lam
      - (Real.cosh A * Real.cosh B * Real.sinh lam + Real.sinh A * Real.sinh B * Real.cosh lam)
      = Real.exp (-lam) * Real.cosh (A - B) := by
    rw [Real.cosh_sub, ← Real.cosh_sub_sinh]
    ring
  have h3 : 0 ≤ Real.exp lam * Real.cosh (A + B) :=
    mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
  have h4 : 0 ≤ Real.exp (-lam) * Real.cosh (A - B) :=
    mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
  constructor <;> linarith

lemma continuous_pairSiteY' : Continuous fun q : ℝ × ℝ × ℝ => pairSiteY' q.1 q.2.1 q.2.2 := by
  unfold pairSiteY'
  refine Continuous.div ?_ ?_ fun q =>
    (cosh_mul_cosh_mul_cosh_add_sinh_mul_sinh_mul_sinh_pos _ _ _).ne'
  · fun_prop
  · fun_prop

/-! ### The one-site branch functions of the marks -/

variable {κ : ℕ} {J : Type*} [Fintype J]

/-- `∂_λ Y_{κ+1}(λ, y₀, y)` for the one-site function of the marks. -/
def pairSiteF' (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ)
    (y₀ : J → ℝ) (y : Fin κ → J → ℝ) : ℝ :=
  pairSiteY' lam (h 0 + pairSiteMark K₀ K y₀ y 0) (h 1 + pairSiteMark K₀ K y₀ y 1)

lemma hasDerivAt_pairSiteF (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) (y : Fin κ → J → ℝ) :
    HasDerivAt (fun l => pairSiteF l h K₀ K y₀ y) (pairSiteF' lam h K₀ K y₀ y) lam :=
  hasDerivAt_pairSiteY _ _ lam

lemma abs_pairSiteF'_le_one (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) (y : Fin κ → J → ℝ) :
    |pairSiteF' lam h K₀ K y₀ y| ≤ 1 :=
  abs_pairSiteY'_le_one _ _ _

lemma continuous_pairSiteMark (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ) (l : Fin 2) :
    Continuous fun q : (J → ℝ) × (Fin κ → J → ℝ) => pairSiteMark K₀ K q.1 q.2 l := by
  unfold pairSiteMark
  fun_prop

/-- Joint continuity of `Y_{κ+1}` in `(λ, y₀, y)`. -/
lemma continuous_pairSiteF_prod (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) :
    Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) => pairSiteF q.1 h K₀ K q.2.1 q.2.2 := by
  unfold pairSiteF pairSiteY
  refine Continuous.log ?_ fun q =>
    (cosh_mul_cosh_mul_cosh_add_sinh_mul_sinh_mul_sinh_pos _ _ _).ne'
  have h0 := (continuous_pairSiteMark K₀ K 0).comp (continuous_snd :
    Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) => q.2)
  have h1 := (continuous_pairSiteMark K₀ K 1).comp (continuous_snd :
    Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) => q.2)
  have hA : Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) =>
      h 0 + pairSiteMark K₀ K q.2.1 q.2.2 0 := continuous_const.add h0
  have hB : Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) =>
      h 1 + pairSiteMark K₀ K q.2.1 q.2.2 1 := continuous_const.add h1
  exact (((Real.continuous_cosh.comp hA).mul (Real.continuous_cosh.comp hB)).mul
    (Real.continuous_cosh.comp continuous_fst)).add
    (((Real.continuous_sinh.comp hA).mul (Real.continuous_sinh.comp hB)).mul
      (Real.continuous_sinh.comp continuous_fst))

/-- Joint continuity of `∂_λ Y_{κ+1}` in `(λ, y₀, y)`. -/
lemma continuous_pairSiteF'_prod (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) :
    Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) =>
      pairSiteF' q.1 h K₀ K q.2.1 q.2.2 := by
  have h0 := (continuous_pairSiteMark K₀ K 0).comp (continuous_snd :
    Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) => q.2)
  have h1 := (continuous_pairSiteMark K₀ K 1).comp (continuous_snd :
    Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) => q.2)
  have hf : Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) =>
      (q.1, (h 0 + pairSiteMark K₀ K q.2.1 q.2.2 0, h 1 + pairSiteMark K₀ K q.2.1 q.2.2 1)) :=
    continuous_fst.prodMk ((continuous_const.add h0).prodMk (continuous_const.add h1))
  have hc := continuous_pairSiteY'.comp hf
  exact hc

/-- **Talagrand's (14.4) for the one-site branch function**: `∫ e^{Y_{κ+1}} d(marks) < ∞`, by the
Gaussian integrals of the four exponentials of (14.142). -/
theorem lintegral_ofReal_exp_pairSiteF_ne_top (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))
      ∂Measure.pi (siteGaussianMarks J κ vs) ≠ ∞ := by
  classical
  -- the four exponentials of (14.142)
  set a : (Fin 2 → Bool) → ℝ := fun ε =>
    isingSpin (ε 0) * (h 0 + ∑ j, K₀ 0 j * y₀ j) + isingSpin (ε 1) * (h 1 + ∑ j, K₀ 1 j * y₀ j)
      + isingSpin (ε 0) * isingSpin (ε 1) * lam with ha
  set B : (Fin 2 → Bool) → Fin κ → J → ℝ := fun ε p j =>
    isingSpin (ε 0) * K p 0 j + isingSpin (ε 1) * K p 1 j with hB
  have hexp : ∀ (ε : Fin 2 → Bool) (y : Fin κ → J → ℝ),
      isingSpin (ε 0) * (h 0 + pairSiteMark K₀ K y₀ y 0)
        + isingSpin (ε 1) * (h 1 + pairSiteMark K₀ K y₀ y 1)
        + isingSpin (ε 0) * isingSpin (ε 1) * lam
      = a ε + ∑ p, ∑ j, B ε p j * y p j := by
    intro ε y
    rw [ha, hB]
    simp only [pairSiteMark]
    have h1 : ∑ p, ∑ j, (isingSpin (ε 0) * K p 0 j + isingSpin (ε 1) * K p 1 j) * y p j
        = isingSpin (ε 0) * (∑ p, ∑ j, K p 0 j * y p j)
          + isingSpin (ε 1) * (∑ p, ∑ j, K p 1 j * y p j) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1]
    ring
  have hpt : ∀ y : Fin κ → J → ℝ, ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))
      = ∑ ε : Fin 2 → Bool, ENNReal.ofReal (1 / 4)
          * ENNReal.ofReal (Real.exp (a ε + ∑ p, ∑ j, B ε p j * y p j)) := by
    intro y
    have hs := sum_exp_pairSpin (h 0 + pairSiteMark K₀ K y₀ y 0) (h 1 + pairSiteMark K₀ K y₀ y 1)
      lam
    simp_rw [hexp] at hs
    rw [pairSiteF, exp_pairSiteY, show Real.cosh (h 0 + pairSiteMark K₀ K y₀ y 0)
        * Real.cosh (h 1 + pairSiteMark K₀ K y₀ y 1) * Real.cosh lam
        + Real.sinh (h 0 + pairSiteMark K₀ K y₀ y 0) * Real.sinh (h 1 + pairSiteMark K₀ K y₀ y 1)
          * Real.sinh lam
        = ∑ ε : Fin 2 → Bool, (1 / 4) * Real.exp (a ε + ∑ p, ∑ j, B ε p j * y p j) by
      rw [← Finset.mul_sum, hs]; ring,
      ENNReal.ofReal_sum_of_nonneg fun ε _ => by positivity]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [ENNReal.ofReal_mul (by norm_num)]
  have hm : ∀ ε : Fin 2 → Bool, Measurable fun y : Fin κ → J → ℝ =>
      ENNReal.ofReal (1 / 4) * ENNReal.ofReal (Real.exp (a ε + ∑ p, ∑ j, B ε p j * y p j)) :=
    fun ε => (measurable_ofReal_exp_add_sum_mul J κ (a ε) (B ε)).const_mul _
  rw [lintegral_congr hpt, lintegral_finsetSum _ fun ε _ => hm ε]
  refine ENNReal.sum_ne_top.2 fun ε _ => ?_
  rw [lintegral_const_mul _ (measurable_ofReal_exp_add_sum_mul J κ (a ε) (B ε)),
    lintegral_ofReal_exp_add_siteGaussianMarks J κ vs (a ε) (B ε)]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

/-- Measurability of the one-site recursion in the root marks. -/
lemma measurable_parisiRec_pairSiteF (ns : Fin κ → ℝ) (vs : Fin κ → ℝ≥0) (lam : ℝ)
    (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ) :
    Measurable fun y₀ : J → ℝ =>
      parisiRec κ ns (siteGaussianMarks J κ vs) (pairSiteF lam h K₀ K y₀) := by
  have hc := (continuous_pairSiteF_prod h K₀ K).comp (continuous_const.prodMk continuous_id :
    Continuous fun q : (J → ℝ) × (Fin κ → J → ℝ) => (lam, q))
  have hG : Measurable (Function.uncurry fun (y₀ : J → ℝ) (y : Fin κ → J → ℝ) =>
      ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))) := by
    have h := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc.measurable)
    exact h
  have hR : Measurable fun y₀ : J → ℝ => cascadeRec κ ns (siteGaussianMarks J κ vs)
      (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))) :=
    measurable_cascadeRec_prod κ ns (siteGaussianMarks J κ vs) hG
  exact hR.ennreal_toReal.log

/-! ### The derivative of `Y₁` and of `Y₀` in `λ` -/

/-- **Talagrand's (14.185), iterated**: `Y₁(λ, y₀)` is differentiable in `λ`, with derivative the
tilted average `𝔼(W₁ ⋯ W_κ ∂_λ Y_{κ+1})`. -/
theorem hasDerivAt_parisiRec_pairSiteF (ns : Fin κ → ℝ) (hpos : ∀ i, 0 < ns i)
    (hle : ∀ i, ns i ≤ 1) (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) :
    HasDerivAt (fun l => parisiRec κ ns (siteGaussianMarks J κ vs) (pairSiteF l h K₀ K y₀))
      (∫ y, pairSiteF' lam h K₀ K y₀ y ∂cascadeTiltMeasure κ ns (siteGaussianMarks J κ vs)
        (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y)))) lam := by
  have hF : Measurable (Function.uncurry fun (l : ℝ) (y : Fin κ → J → ℝ) =>
      pairSiteF l h K₀ K y₀ y) := by
    have hc := (continuous_pairSiteF_prod h K₀ K).comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd) :
        Continuous fun q : ℝ × (Fin κ → J → ℝ) => (q.1, (y₀, q.2)))
    exact hc.measurable
  have hF' : Measurable (Function.uncurry fun (l : ℝ) (y : Fin κ → J → ℝ) =>
      pairSiteF' l h K₀ K y₀ y) := by
    have hc := (continuous_pairSiteF'_prod h K₀ K).comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd) :
        Continuous fun q : ℝ × (Fin κ → J → ℝ) => (q.1, (y₀, q.2)))
    exact hc.measurable
  exact hasDerivAt_parisiRec κ ns (siteGaussianMarks J κ vs)
    (fun l => hF.comp (measurable_const.prodMk measurable_id))
    (fun l => hF'.comp (measurable_const.prodMk measurable_id))
    (fun l y => hasDerivAt_pairSiteF l h K₀ K y₀ y) (C := 1)
    (fun l y => abs_pairSiteF'_le_one l h K₀ K y₀ y) hpos hle
    (lintegral_ofReal_exp_pairSiteF_ne_top vs lam h K₀ K y₀)

/-- The tilted measure of the one-site branch function is a probability measure. -/
lemma isProbabilityMeasure_cascadeTiltMeasure_pairSiteF (ns : Fin κ → ℝ) (hpos : ∀ i, 0 < ns i)
    (hle : ∀ i, ns i ≤ 1) (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) :
    IsProbabilityMeasure (cascadeTiltMeasure κ ns (siteGaussianMarks J κ vs)
      (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y)))) :=
  isProbabilityMeasure_cascadeTiltMeasure κ ns _
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_pairSiteF' lam h K₀ K y₀)))
    (fun _ => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos hle
    (lintegral_ofReal_exp_pairSiteF_ne_top vs lam h K₀ K y₀)

/-- `|∂_λ Y₁(λ, y₀)| ≤ 1`. -/
lemma abs_integral_pairSiteF'_le_one (ns : Fin κ → ℝ) (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1)
    (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) :
    |∫ y, pairSiteF' lam h K₀ K y₀ y ∂cascadeTiltMeasure κ ns (siteGaussianMarks J κ vs)
      (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y)))| ≤ 1 := by
  have := isProbabilityMeasure_cascadeTiltMeasure_pairSiteF ns hpos hle vs lam h K₀ K y₀
  have hb := norm_integral_le_of_norm_le_const
    (μ := cascadeTiltMeasure κ ns (siteGaussianMarks J κ vs)
      (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))))
    (f := fun y => pairSiteF' lam h K₀ K y₀ y) (C := 1)
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact abs_pairSiteF'_le_one _ _ _ _ _ _)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at hb

universe u

variable {J' : Type u} [Fintype J']

/-- `Y₁(λ, ·)` is integrable in the root marks (the one-site case of
`integrable_parisiRec_pairCoshF_rootMarksLaw`). -/
theorem integrable_parisiRec_pairSiteF (ns : Fin κ → ℝ) (hpos : ∀ i, 0 < ns i)
    (hle : ∀ i, ns i ≤ 1) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (lam : ℝ)
    (h : Fin 2 → ℝ) (K₀ : Fin 2 → J' → ℝ) (K : Fin κ → Fin 2 → J' → ℝ) :
    Integrable (fun y₀ : J' → ℝ =>
        parisiRec κ ns (siteGaussianMarks J' κ vs) (pairSiteF lam h K₀ K y₀))
      (Measure.pi fun _ : J' => gaussianReal 0 v₀) := by
  have hI := integrable_parisiRec_pairCoshF_rootMarksLaw 1 ns hpos hle lam (fun s => h s.2)
    K₀ K v₀ vs
  have hpt : ∀ z₀ : Fin 1 × J' → ℝ, parisiRec κ ns (siteGaussianMarks (Fin 1 × J') κ vs)
      (pairCoshF 1 κ lam (fun s => h s.2) K₀ K z₀)
      = parisiRec κ ns (siteGaussianMarks J' κ vs) (pairSiteF lam h K₀ K (fun j => z₀ (0, j))) := by
    intro z₀
    rw [parisiRec_pairCoshF 1 ns hpos hle vs lam (fun s => h s.2) K₀ K z₀,
      Fin.sum_univ_one]
  have hg : Function.Injective fun j : J' => ((0 : Fin 1), j) :=
    fun j j' hjj' => (Prod.mk.inj hjj').2
  have hmp : MeasurePreserving (fun z₀ : Fin 1 × J' → ℝ => fun j => z₀ (0, j))
      (rootMarksLaw 1 v₀) (Measure.pi fun _ : J' => gaussianReal 0 v₀) :=
    measurePreserving_comp_pi_of_injective (gaussianReal 0 v₀) hg
  rw [← hmp.integrable_comp (measurable_parisiRec_pairSiteF ns vs lam h K₀ K).aestronglyMeasurable]
  exact hI.congr (Filter.Eventually.of_forall fun z₀ => hpt z₀)

/-- **The derivative of Talagrand's `Y₀(λ)`**: `Y₀'(λ) = 𝔼_{y₀} 𝔼(W₁ ⋯ W_κ ∂_λ Y_{κ+1})`. -/
def pairSiteY₀' (ns : Fin κ → ℝ) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ) : ℝ :=
  ∫ y₀, (∫ y, pairSiteF' lam h K₀ K y₀ y ∂cascadeTiltMeasure κ ns (siteGaussianMarks J κ vs)
      (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))))
    ∂Measure.pi fun _ : J => gaussianReal 0 v₀

/-- **`Y₀` is differentiable in `λ`**, with derivative `Y₀'(λ) = 𝔼_{y₀} 𝔼(W₁ ⋯ W_κ ∂_λ Y_{κ+1})`. -/
theorem hasDerivAt_pairSiteY₀ (ns : Fin κ → ℝ) (hpos : ∀ i, 0 < ns i)
    (hle : ∀ i, ns i ≤ 1) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ)
    (K₀ : Fin 2 → J' → ℝ) (K : Fin κ → Fin 2 → J' → ℝ) :
    HasDerivAt (fun l => pairSiteY₀ ns v₀ vs l h K₀ K) (pairSiteY₀' ns v₀ vs lam h K₀ K) lam := by
  -- measurability of the derivative in the root marks, through the density
  have hF'meas : AEStronglyMeasurable (fun y₀ : J' → ℝ =>
      ∫ y, pairSiteF' lam h K₀ K y₀ y ∂cascadeTiltMeasure κ ns (siteGaussianMarks J' κ vs)
        (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))))
      (Measure.pi fun _ : J' => gaussianReal 0 v₀) := by
    have hG : Measurable (Function.uncurry fun (y₀ : J' → ℝ) (y : Fin κ → J' → ℝ) =>
        ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))) := by
      have hc := (continuous_pairSiteF_prod h K₀ K).comp (continuous_const.prodMk continuous_id :
        Continuous fun q : (J' → ℝ) × (Fin κ → J' → ℝ) => (lam, q))
      have h := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc.measurable)
      exact h
    have hF'm : Measurable fun q : (J' → ℝ) × (Fin κ → J' → ℝ) =>
        pairSiteF' lam h K₀ K q.1 q.2 := by
      have hc := (continuous_pairSiteF'_prod h K₀ K).comp (continuous_const.prodMk continuous_id :
        Continuous fun q : (J' → ℝ) × (Fin κ → J' → ℝ) => (lam, q))
      exact hc.measurable
    have hjoint : Measurable fun q : (J' → ℝ) × (Fin κ → J' → ℝ) =>
        (cascadeTiltDensity κ ns (siteGaussianMarks J' κ vs)
          (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K q.1 y))) q.2).toReal
          * pairSiteF' lam h K₀ K q.1 q.2 :=
      (measurable_cascadeTiltDensity_prod κ ns (siteGaussianMarks J' κ vs)
        hG).ennreal_toReal.mul hF'm
    have hsm' := hjoint.stronglyMeasurable.integral_prod_right'
      (ν := Measure.pi (siteGaussianMarks J' κ vs))
    refine hsm'.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun y₀ => ?_)
    have hGy : Measurable fun y : Fin κ → J' → ℝ =>
        ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y)) := by
      have := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_pairSiteF' lam h K₀ K y₀))
      exact this
    show (∫ y, (cascadeTiltDensity κ ns (siteGaussianMarks J' κ vs)
        (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))) y).toReal
          * pairSiteF' lam h K₀ K y₀ y ∂Measure.pi (siteGaussianMarks J' κ vs))
      = ∫ y, pairSiteF' lam h K₀ K y₀ y ∂cascadeTiltMeasure κ ns (siteGaussianMarks J' κ vs)
          (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y)))
    rw [integral_cascadeTiltMeasure κ ns (siteGaussianMarks J' κ vs)
      (G := fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))) hGy
      (fun _ => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos hle
      (lintegral_ofReal_exp_pairSiteF_ne_top vs lam h K₀ K y₀)]
    simp only [smul_eq_mul]
  unfold pairSiteY₀ pairSiteY₀'
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := Measure.pi fun _ : J' => gaussianReal 0 v₀) (s := Set.univ)
    (F := fun l y₀ => parisiRec κ ns (siteGaussianMarks J' κ vs) (pairSiteF l h K₀ K y₀))
    (F' := fun l y₀ => ∫ y, pairSiteF' l h K₀ K y₀ y
      ∂cascadeTiltMeasure κ ns (siteGaussianMarks J' κ vs)
        (fun y => ENNReal.ofReal (Real.exp (pairSiteF l h K₀ K y₀ y))))
    (bound := fun _ => 1) Filter.univ_mem
    (Filter.Eventually.of_forall fun l =>
      (measurable_parisiRec_pairSiteF ns vs l h K₀ K).aestronglyMeasurable)
    (integrable_parisiRec_pairSiteF ns hpos hle v₀ vs lam h K₀ K) hF'meas
    (Filter.Eventually.of_forall fun y₀ l _ => by
      rw [Real.norm_eq_abs]; exact abs_integral_pairSiteF'_le_one ns hpos hle vs l h K₀ K y₀)
    (integrable_const _)
    (Filter.Eventually.of_forall fun y₀ l _ =>
      hasDerivAt_parisiRec_pairSiteF ns hpos hle vs l h K₀ K y₀)).2

/-- `|Y₀'(λ)| ≤ 1`. -/
theorem abs_pairSiteY₀'_le_one (ns : Fin κ → ℝ) (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1)
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) :
    |pairSiteY₀' ns v₀ vs lam h K₀ K| ≤ 1 := by
  unfold pairSiteY₀'
  have hb := norm_integral_le_of_norm_le_const (μ := Measure.pi fun _ : J => gaussianReal 0 v₀)
    (C := 1) (Filter.Eventually.of_forall fun y₀ => by
      rw [Real.norm_eq_abs]; exact abs_integral_pairSiteF'_le_one ns hpos hle vs lam h K₀ K y₀)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at hb

end

end SpinGlass

/-!
### Coordinatewise transport of cascade tilts

The proof of Proposition 14.6.4(a), equation (14.177), compares two descriptions of the same
coupled cascade.
The Gaussian marks used by `pairSiteY₀` are functions `Fin 2 → ℝ`; the square appearing in
Talagrand's formula is expressed using pairs `ℝ × ℝ`.  We first prove that `cascadeTilt` is
unchanged when every mark law and every observable are transported by measurable maps.  We
then apply this fact to `MeasurableEquiv.finTwoArrow` and to the level-dependent coupling maps.
-/

namespace ProbabilityTheory

universe u v

noncomputable section

/-- Push each mark law forward by the map assigned to that coordinate.

The measurability proof is retained as an argument so that the probability-measure instance for
the pushforward family can be synthesized without introducing a separate local instance at each
use site. -/
private def coordinateMapLaw
    {T : Type u} {T' : Type v}
    [MeasurableSpace T] [MeasurableSpace T']
    {k : ℕ}
    (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)]
    (φ : Fin k → T → T')
    (_hφ : ∀ i, Measurable (φ i))
    (i : Fin k) : Measure T' :=
  (μs i).map (φ i)

/-- Coordinatewise pushforwards of probability laws are probability laws. -/
private instance coordinateMapLaw_isProbabilityMeasure
    {T : Type u} {T' : Type v}
    [MeasurableSpace T] [MeasurableSpace T']
    {k : ℕ}
    (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)]
    (φ : Fin k → T → T')
    (hφ : ∀ i, Measurable (φ i))
    (i : Fin k) :
    IsProbabilityMeasure (coordinateMapLaw μs φ hφ i) := by
  unfold coordinateMapLaw
  exact Measure.isProbabilityMeasure_map (hφ i).aemeasurable

/-- Applying the coordinate maps after `Fin.cons` agrees with mapping the head and tail
separately. -/
private lemma coordinateMap_cons
    {T : Type u} {T' : Type v}
    {k : ℕ}
    (φ : Fin (k + 1) → T → T')
    (z : T) (ys : Fin k → T) :
    (fun i => φ i ((Fin.cons z ys : Fin (k + 1) → T) i))
      =
    Fin.cons (φ 0 z) (fun i => φ i.succ (ys i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

/-- The first cascade weight commutes with coordinatewise transport.

The denominator follows from `cascadeRec_map` on all coordinates.  The numerator follows from
the same theorem on the tail coordinates, after rewriting the mapped `Fin.cons`. -/
private lemma cascadeW_coordinateMap
    {T : Type u} {T' : Type v}
    [MeasurableSpace T] [MeasurableSpace T']
    {k : ℕ}
    (ms : Fin (k + 1) → ℝ)
    (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)]
    (φ : Fin (k + 1) → T → T')
    (hφ : ∀ i, Measurable (φ i))
    {G : (Fin (k + 1) → T') → ℝ≥0∞}
    (hG : Measurable G)
    (z : T) :
    cascadeW k ms (coordinateMapLaw μs φ hφ) G (φ 0 z)
      =
    cascadeW k ms μs
      (fun zs => G (fun i => φ i (zs i))) z := by
  have hden :
      cascadeRec (k + 1) ms (coordinateMapLaw μs φ hφ) G
        =
      cascadeRec (k + 1) ms μs
        (fun zs => G (fun i => φ i (zs i))) := by
    change cascadeRec (k + 1) ms
      (fun i => (μs i).map (φ i)) G = _
    exact cascadeRec_map (T := T) (T' := T') (k + 1)
      ms μs φ hφ hG
  have hGz :
      Measurable fun ys : Fin k → T' => G (Fin.cons (φ 0 z) ys) :=
    hG.comp
      (measurable_fin_cons.comp
        (measurable_const.prodMk measurable_id))
  have hnum :
      cascadeRec k (Fin.tail ms)
          (Fin.tail (coordinateMapLaw μs φ hφ))
          (fun ys => G (Fin.cons (φ 0 z) ys))
        =
      cascadeRec k (Fin.tail ms) (Fin.tail μs)
          (fun ys => G (fun i =>
            φ i ((Fin.cons z ys : Fin (k + 1) → T) i))) := by
    change cascadeRec k (Fin.tail ms)
      (fun i => ((Fin.tail μs) i).map ((Fin.tail φ) i))
      (fun ys => G (Fin.cons (φ 0 z) ys)) = _
    have h := cascadeRec_map (T := T) (T' := T') k
      (Fin.tail ms) (Fin.tail μs) (Fin.tail φ)
      (fun i => hφ i.succ) hGz
    simpa only [Fin.tail, coordinateMap_cons] using h
  unfold cascadeW
  rw [hnum, hden]

/-- A cascade tilt computed with pushed-forward mark laws equals the original tilt applied to
the pulled-back weight and observable. -/
private theorem cascadeTilt_coordinateMap
    {T : Type u} {T' : Type v}
    [MeasurableSpace T] [MeasurableSpace T']
    (k : ℕ) :
    ∀ (ms : Fin k → ℝ)
      (μs : Fin k → Measure T)
      [∀ i, IsProbabilityMeasure (μs i)]
      (φ : Fin k → T → T')
      (hφ : ∀ i, Measurable (φ i))
      {G A : (Fin k → T') → ℝ≥0∞},
      Measurable G → Measurable A →
      cascadeTilt k ms (coordinateMapLaw μs φ hφ) G A
        =
      cascadeTilt k ms μs
        (fun zs => G (fun i => φ i (zs i)))
        (fun zs => A (fun i => φ i (zs i))) := by
  induction k with
  | zero =>
      intro ms μs _ φ hφ G A hG hA
      rw [cascadeTilt_zero, cascadeTilt_zero]
      exact congrArg A (Subsingleton.elim _ _)
  | succ k ih =>
      intro ms μs _ φ hφ G A hG hA
      rw [cascadeTilt_succ, cascadeTilt_succ]
      -- This is the integrand required by `lintegral_map` at the first level.
      have hM :
          Measurable fun z : T' =>
            cascadeW k ms (coordinateMapLaw μs φ hφ) G z *
            cascadeTilt k (Fin.tail ms)
              (Fin.tail (coordinateMapLaw μs φ hφ))
              (fun ys => G (Fin.cons z ys))
              (fun ys => A (Fin.cons z ys)) := by
        exact
          (measurable_cascadeW k ms
            (coordinateMapLaw μs φ hφ) hG).mul
          (measurable_cascadeTilt_prod k
            (Fin.tail ms)
            (Fin.tail (coordinateMapLaw μs φ hφ))
            (Gs := fun z ys => G (Fin.cons z ys))
            (As := fun z ys => A (Fin.cons z ys))
            (hG.comp measurable_fin_cons)
            (hA.comp measurable_fin_cons))
      change (∫⁻ z,
        cascadeW k ms (coordinateMapLaw μs φ hφ) G z *
          cascadeTilt k (Fin.tail ms)
            (Fin.tail (coordinateMapLaw μs φ hφ))
            (fun ys => G (Fin.cons z ys))
            (fun ys => A (Fin.cons z ys))
        ∂(μs 0).map (φ 0)) = _
      rw [lintegral_map hM (hφ 0)]
      refine lintegral_congr fun z => ?_
      rw [cascadeW_coordinateMap ms μs φ hφ hG z]
      -- The remaining coordinates are transported by the tail of `φ`.
      have hinner := ih
        (Fin.tail ms) (Fin.tail μs) (Fin.tail φ)
        (fun i => hφ i.succ)
        (G := fun ys => G (Fin.cons (φ 0 z) ys))
        (A := fun ys => A (Fin.cons (φ 0 z) ys))
        (hG.comp
          (measurable_fin_cons.comp
            (measurable_const.prodMk measurable_id)))
        (hA.comp
          (measurable_fin_cons.comp
            (measurable_const.prodMk measurable_id)))
      let _ : ∀ i, IsProbabilityMeasure
          (coordinateMapLaw (Fin.tail μs) (Fin.tail φ)
            (fun i => hφ i.succ) i) :=
        fun i => coordinateMapLaw_isProbabilityMeasure
          (Fin.tail μs) (Fin.tail φ) (fun i => hφ i.succ) i
      change _ * cascadeTilt k (Fin.tail ms)
        (coordinateMapLaw (Fin.tail μs) (Fin.tail φ)
          (fun i => hφ i.succ))
        (fun ys => G (Fin.cons (φ 0 z) ys))
        (fun ys => A (Fin.cons (φ 0 z) ys)) = _
      rw [hinner]
      simp only [Fin.tail, coordinateMap_cons]

/-- Pulling the paired cascade back through `couplingMap` turns the product observable into the
tilted conditional square.

The proof first transports independent raw pairs to `pairMarkLaw`, then uses
`cascadeTiltPair_eq_cascadeTilt` and Talagrand's product identity `cascadeTiltPair_prod`. -/
private theorem cascadeTilt_coupling_prod
    {T : Type u}
    [MeasurableSpace T]
    (k r : ℕ)
    (ms : Fin k → ℝ)
    (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)]
    {G A : (Fin k → T) → ℝ≥0∞}
    (hG : Measurable G)
    (hA : Measurable A)
    (hGpos : ∀ zs, 0 < G zs)
    (hpos : ∀ i, 0 < ms i) :
    cascadeTilt k
        (halveBelow r ms)
        (fun p => (μs p).prod (μs p))
        (fun zs =>
          G (fun i => (couplingMap r i (zs i)).1)
            *
          G (fun i => (couplingMap r i (zs i)).2))
        (fun zs =>
          A (fun i => (couplingMap r i (zs i)).1)
            *
          A (fun i => (couplingMap r i (zs i)).2))
      =
    cascadeTiltSq k r ms μs G A := by
  set G₂ : (Fin k → T × T) → ℝ≥0∞ :=
    fun zs =>
      G (fun i => (zs i).1) *
      G (fun i => (zs i).2)
  set A₂ : (Fin k → T × T) → ℝ≥0∞ :=
    fun zs =>
      A (fun i => (zs i).1) *
      A (fun i => (zs i).2)
  have hG₂ : Measurable G₂ := by
    dsimp [G₂]
    exact (hG.comp measurable_pairFst).mul (hG.comp measurable_pairSnd)
  have hA₂ : Measurable A₂ := by
    dsimp [A₂]
    exact (hA.comp measurable_pairFst).mul (hA.comp measurable_pairSnd)
  let μprod : Fin k → Measure (T × T) :=
    fun p => (μs p).prod (μs p)
  let φ : Fin k → (T × T) → (T × T) :=
    fun p => couplingMap r p
  have hφ : ∀ i, Measurable (φ i) :=
    fun i => measurable_couplingMap r i
  have hmap :
      coordinateMapLaw μprod φ hφ
        =
      pairMarkLaw r μs := by
    funext p
    change
      ((μs p).prod (μs p)).map (couplingMap r p)
        =
      pairMarkLaw r μs p
    exact congrFun
      (map_couplingMap_prod_eq_pairMarkLaw r μs) p
  calc
    cascadeTilt k
        (halveBelow r ms)
        (fun p => (μs p).prod (μs p))
        (fun zs =>
          G (fun i => (couplingMap r i (zs i)).1)
            *
          G (fun i => (couplingMap r i (zs i)).2))
        (fun zs =>
          A (fun i => (couplingMap r i (zs i)).1)
            *
          A (fun i => (couplingMap r i (zs i)).2))
        =
      cascadeTilt k
        (halveBelow r ms)
        (coordinateMapLaw μprod φ hφ)
        G₂ A₂ := by
          symm
          simpa [μprod, φ, G₂, A₂] using
            (cascadeTilt_coordinateMap
              (T := T × T) (T' := T × T) k
              (halveBelow r ms)
              μprod φ hφ hG₂ hA₂)
    _ =
      cascadeTilt k
        (halveBelow r ms)
        (pairMarkLaw r μs)
        G₂ A₂ := by
          exact cascadeTilt_congr_measure
            (halveBelow r ms) hmap G₂ A₂
    _ =
      cascadeTiltPair k r ms μs G A₂ := by
          symm
          exact cascadeTiltPair_eq_cascadeTilt
            k r ms μs hG hA₂ hGpos hpos
    _ =
      cascadeTiltSq k r ms μs G A := by
          exact cascadeTiltPair_prod
            k r ms μs hG hA

end

end ProbabilityTheory

/-!
### Terminal derivative at `λ = 0`

We first identify the terminal derivative pointwise.  The analytic facts needed to integrate that
identity are recorded afterward, before the nonnegative encoding of the signed square.
-/

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable {κ : ℕ}

/-- At `λ = 0`, the derivative of the two-copy terminal function is the product of the two
magnetizations. -/
@[simp] lemma pairSiteY'_zero (A B : ℝ) :
    pairSiteY' 0 A B = Real.tanh A * Real.tanh B := by
  unfold pairSiteY'
  rw [Real.sinh_zero, Real.cosh_zero]
  simp only [mul_zero, mul_one, zero_add, add_zero]
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  field_simp [ne_of_gt (Real.cosh_pos A), ne_of_gt (Real.cosh_pos B)]

/-- Consequently, the terminal derivative observable is the product of the magnetizations in
the two effective fields. -/
@[simp] lemma pairSiteF'_zero
    {J : Type*} [Fintype J]
    (h : Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ)
    (y₀ : J → ℝ)
    (y : Fin κ → J → ℝ) :
    pairSiteF' 0 h K₀ K y₀ y
      = Real.tanh (h 0 + pairSiteMark K₀ K y₀ y 0)
        * Real.tanh (h 1 + pairSiteMark K₀ K y₀ y 1) := by
  simp [pairSiteF', pairSiteY'_zero]

/-- Continuity of the hyperbolic tangent in the form used below. -/
private lemma continuous_tanh' : Continuous Real.tanh := by
  have hcosh : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
  convert Real.continuous_sinh.div₀ Real.continuous_cosh hcosh with x
  exact Real.tanh_eq_sinh_div_cosh x

/-- Continuity of each coupled terminal magnetization as a function of the Gaussian marks. -/
private lemma continuous_pairSiteTanhField_coupling
    (h : ℝ) (y₀ : Fin 2 → ℝ) (τ : ℕ) (l : Fin 2) :
    Continuous fun y : Fin κ → Fin 2 → ℝ =>
      Real.tanh (h + pairSiteMark (couplingFactorSgn 1 τ 0)
        (fun p => couplingFactorSgn 1 τ (p.val + 1)) y₀ y l) :=
  continuous_tanh'.comp <|
    continuous_const.add <| (continuous_pairSiteMark
      (couplingFactorSgn 1 τ 0)
      (fun p => couplingFactorSgn 1 τ (p.val + 1)) l).comp
        (continuous_const.prodMk continuous_id)

/-- If `-1 < t₀, t₁ < 1` and `1 ≤ c`, then `(t₀ + c) (t₁ + c)` is measurable,
nonnegative, and bounded by `(c + 1)²`; hence it is integrable under a probability law. -/
private lemma integrable_shift_mul_of_mem_Ioo
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (t₀ t₁ : X → ℝ) (ht₀ : Measurable t₀) (ht₁ : Measurable t₁)
    (ht₀lo : ∀ x, -1 < t₀ x) (ht₀hi : ∀ x, t₀ x < 1)
    (ht₁lo : ∀ x, -1 < t₁ x) (ht₁hi : ∀ x, t₁ x < 1)
    (c : ℝ) (hc : 1 ≤ c) :
    Integrable (fun x => (t₀ x + c) * (t₁ x + c)) μ := by
  refine Integrable.of_bound
    ((ht₀.add measurable_const).mul (ht₁.add measurable_const)).aestronglyMeasurable
    ((c + 1) ^ 2) (Filter.Eventually.of_forall fun x => ?_)
  have h₀nonneg : 0 ≤ t₀ x + c := by linarith [ht₀lo x]
  have h₁nonneg : 0 ≤ t₁ x + c := by linarith [ht₁lo x]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h₀nonneg h₁nonneg)]
  calc
    (t₀ x + c) * (t₁ x + c) ≤ (c + 1) * (t₁ x + c) :=
      mul_le_mul_of_nonneg_right (by linarith [ht₀hi x]) h₁nonneg
    _ ≤ (c + 1) * (c + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [ht₁hi x]) (by linarith)
    _ = (c + 1) ^ 2 := by ring

/-- The one-copy terminal weight `exp (log cosh (a + ∑ zₚ))`, encoded in `ℝ≥0∞`. -/
private def logCoshWeight
    (a : ℝ)
    (z : Fin κ → ℝ) :
    ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp
      (Real.log
        (Real.cosh
          (a + ∑ p, z p))))

/-- The shifted one-copy magnetization `tanh (a + ∑ zₚ) + c`, encoded in `ℝ≥0∞`.
Only `c = 1` and `c = 2` are used below, so the argument of `ENNReal.ofReal` is nonnegative. -/
private def shiftedTanhWeight
    (c a : ℝ)
    (z : Fin κ → ℝ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (Real.tanh (a + ∑ p, z p) + c)

/-- Measurability of the one-copy Boltzmann factor. -/
private lemma measurable_logCoshWeight
    (a : ℝ) :
    Measurable (logCoshWeight (κ := κ) a) := by
  unfold logCoshWeight
  exact
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp
        (Real.measurable_log.comp
          (Real.continuous_cosh.measurable.comp
            (measurable_const.add
              (Finset.measurable_sum _
                fun p _ => measurable_pi_apply p)))))

/-- Measurability of the shifted terminal magnetization. -/
private lemma measurable_shiftedTanhWeight
    (c a : ℝ) :
    Measurable (shiftedTanhWeight (κ := κ) c a) := by
  unfold shiftedTanhWeight
  exact
    ENNReal.measurable_ofReal.comp
      ((continuous_tanh'.measurable.comp
        (measurable_const.add (Finset.measurable_sum _
          fun p _ => measurable_pi_apply p))).add measurable_const)

/-!
### From the coupled tilt to the signed square

The coupled cascade machinery is `ℝ≥0∞`-valued, while the terminal magnetization is signed.
We therefore compute two nonnegative shifted squares and recover the signed product by an
algebraic identity.  This section first defines that encoding, then identifies the coupled
terminal tilt with it, and finally returns to a real-valued integral.
-/

/-- Talagrand's signed conditional square
`𝔼(W₁ ⋯ W_r (𝔼_{r+1}(W_{r+1} ⋯ W_κ tanh(a + ∑ z_p)))²)`.

`cascadeTiltSq` only accepts `ℝ≥0∞`-valued observables.  The definition therefore uses the
nonnegative observables `tanh + 1` and `tanh + 2`, then recovers the signed product from
`x * y = 2 * (x + 1) * (y + 1) - (x + 2) * (y + 2) + 2`.  For `r = τ - 1`, the inner
conditional tilted average is Talagrand's `D'_τ(ζ_τ)`, and the outer `r` levels provide the
prefix weights in (14.177). -/
noncomputable def cascadeTiltTanhSq
    (ms : Fin κ → ℝ)
    (vs : Fin κ → ℝ≥0)
    (r : ℕ)
    (a : ℝ) :
    ℝ :=
  2 *
      (cascadeTiltSq κ r ms
        (fun p => gaussianReal 0 (vs p))
        (logCoshWeight (κ := κ) a)
        (shiftedTanhWeight (κ := κ) 1 a)).toReal
    -
      (cascadeTiltSq κ r ms
        (fun p => gaussianReal 0 (vs p))
        (logCoshWeight (κ := κ) a)
        (shiftedTanhWeight (κ := κ) 2 a)).toReal
    + 2

/-- The encoded signed conditional square is measurable in the root field `a`. -/
private lemma measurable_cascadeTiltTanhSq
    (ms : Fin κ → ℝ)
    (vs : Fin κ → ℝ≥0)
    (r : ℕ) :
    Measurable (cascadeTiltTanhSq ms vs r) := by
  have hsum : Measurable fun q : ℝ × (Fin κ → ℝ) => q.1 + ∑ p, q.2 p :=
    measurable_fst.add <|
      Finset.measurable_sum _ fun p _ =>
        (measurable_pi_apply p).comp measurable_snd
  have hG : Measurable (Function.uncurry fun a => logCoshWeight (κ := κ) a) := by
    exact ENNReal.measurable_ofReal.comp <|
      Real.measurable_exp.comp <|
        Real.measurable_log.comp <|
          Real.continuous_cosh.measurable.comp hsum
  have hA (c : ℝ) :
      Measurable (Function.uncurry fun a => shiftedTanhWeight (κ := κ) c a) := by
    exact ENNReal.measurable_ofReal.comp <|
      ((continuous_tanh'.measurable.comp hsum).add measurable_const)
  have hsq (c : ℝ) : Measurable fun a =>
      cascadeTiltSq κ r ms
        (fun p => gaussianReal 0 (vs p))
        (logCoshWeight (κ := κ) a)
        (shiftedTanhWeight (κ := κ) c a) :=
    measurable_cascadeTiltSq_prod κ r ms
      (fun p => gaussianReal 0 (vs p)) hG (hA c)
  unfold cascadeTiltTanhSq
  exact ((hsq 1).ennreal_toReal.const_mul 2).sub
    (hsq 2).ennreal_toReal |>.add_const 2

/-- The coupled tilt of `(tanh + c)` on the two branches is the tilted conditional square of
the one-copy observable `tanh + c`.

The argument has three changes of coordinates: identify `Fin 2 → ℝ` with `ℝ × ℝ`, push the
independent pair laws through `couplingMap (τ - 1)`, and invoke the coupled-product identity.
The two terminal-field lemmas from `CoupledLambdaZero` identify the resulting branch fields. -/
private lemma cascadeTilt_pairSite_zero_shift
    (ms : Fin κ → ℝ)
    (hpos : ∀ i, 0 < ms i)
    (vs : Fin κ → ℝ≥0)
    (h : ℝ)
    (y₀ : Fin 2 → ℝ)
    {τ : ℕ}
    (hτ : 1 ≤ τ)
    (c : ℝ) :
    cascadeTilt κ
      (halveBelow (τ - 1) ms)
      (siteGaussianMarks (Fin 2) κ vs)
      (fun y =>
        ENNReal.ofReal
          (Real.exp
            (pairSiteF 0 (fun _ => h)
              (couplingFactorSgn 1 τ 0)
              (fun p =>
                couplingFactorSgn 1 τ (p.val + 1))
              y₀ y)))
      (fun y =>
        ENNReal.ofReal
          (Real.tanh
            (h +
              pairSiteMark
                (couplingFactorSgn 1 τ 0)
                (fun p =>
                  couplingFactorSgn 1 τ (p.val + 1))
                y₀ y 0)
            + c)
          *
        ENNReal.ofReal
          (Real.tanh
            (h +
              pairSiteMark
                (couplingFactorSgn 1 τ 0)
                (fun p =>
                  couplingFactorSgn 1 τ (p.val + 1))
                y₀ y 1)
            + c))
      =
    cascadeTiltSq κ (τ - 1) ms
      (fun p => gaussianReal 0 (vs p))
      (logCoshWeight (κ := κ) (h + y₀ 0))
      (shiftedTanhWeight (κ := κ) c (h + y₀ 0)) := by
  set G : (Fin κ → ℝ) → ℝ≥0∞ :=
    logCoshWeight (κ := κ) (h + y₀ 0)
  set A : (Fin κ → ℝ) → ℝ≥0∞ :=
    shiftedTanhWeight (κ := κ) c (h + y₀ 0)
  have hG : Measurable G :=
    measurable_logCoshWeight (κ := κ) (h + y₀ 0)
  have hA : Measurable A :=
    measurable_shiftedTanhWeight (κ := κ) c (h + y₀ 0)
  have hGpos : ∀ z, 0 < G z := by
    intro z
    dsimp [G, logCoshWeight]
    exact ENNReal.ofReal_pos.2 (Real.exp_pos _)
  -- Pull the product weight and product observable back through the coupling maps.
  set Ĝ : (Fin κ → ℝ × ℝ) → ℝ≥0∞ :=
    fun zs =>
      G (fun i =>
        (couplingMap (τ - 1) i (zs i)).1)
        *
      G (fun i =>
        (couplingMap (τ - 1) i (zs i)).2)
  set Â : (Fin κ → ℝ × ℝ) → ℝ≥0∞ :=
    fun zs =>
      A (fun i =>
        (couplingMap (τ - 1) i (zs i)).1)
        *
      A (fun i =>
        (couplingMap (τ - 1) i (zs i)).2)
  have hĜ : Measurable Ĝ := by
    dsimp [Ĝ]
    exact
      (hG.comp
        (measurable_pi_lambda _ fun i =>
          measurable_fst.comp
            ((measurable_couplingMap
              (τ - 1) i).comp
                (measurable_pi_apply i)))).mul
      (hG.comp
        (measurable_pi_lambda _ fun i =>
          measurable_snd.comp
            ((measurable_couplingMap
              (τ - 1) i).comp
                (measurable_pi_apply i))))
  have hÂ : Measurable Â := by
    dsimp [Â]
    exact
      (hA.comp
        (measurable_pi_lambda _ fun i =>
          measurable_fst.comp
            ((measurable_couplingMap
              (τ - 1) i).comp
                (measurable_pi_apply i)))).mul
      (hA.comp
        (measurable_pi_lambda _ fun i =>
          measurable_snd.comp
            ((measurable_couplingMap
              (τ - 1) i).comp
                (measurable_pi_apply i))))
  -- At `λ = 0`, the two-copy terminal weight factors into the two one-copy weights.
  have hF :
      (fun y : Fin κ → Fin 2 → ℝ =>
        ENNReal.ofReal
          (Real.exp
            (pairSiteF 0 (fun _ => h)
              (couplingFactorSgn 1 τ 0)
              (fun p =>
                couplingFactorSgn 1 τ (p.val + 1))
              y₀ y)))
        =
      fun y =>
        Ĝ (fun i =>
          MeasurableEquiv.finTwoArrow (y i)) := by
    funext y
    simp only [Ĝ]
    simp only [G, logCoshWeight]
    rw [pairSiteF, pairSiteY_zero,
      pairSiteMark_couplingFactorSgn_one_zero
        hτ,
      pairSiteMark_couplingFactorSgn_one_one
        hτ,
      Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    simp only [← add_assoc]
    rfl
  -- The shifted terminal observable factors in the same coordinates.
  have hObs :
      (fun y : Fin κ → Fin 2 → ℝ =>
        ENNReal.ofReal
          (Real.tanh
            (h +
              pairSiteMark
                (couplingFactorSgn 1 τ 0)
                (fun p =>
                  couplingFactorSgn 1 τ (p.val + 1))
                y₀ y 0)
            + c)
          *
        ENNReal.ofReal
          (Real.tanh
            (h +
              pairSiteMark
                (couplingFactorSgn 1 τ 0)
                (fun p =>
                  couplingFactorSgn 1 τ (p.val + 1))
                y₀ y 1)
            + c))
        =
      fun y =>
        Â (fun i =>
          MeasurableEquiv.finTwoArrow (y i)) := by
    funext y
    simp only [Â]
    simp only [A, shiftedTanhWeight]
    rw [pairSiteMark_couplingFactorSgn_one_zero
        hτ,
      pairSiteMark_couplingFactorSgn_one_one
        hτ]
    simp only [← add_assoc]
    rfl
  have hArrow :
      ∀ _ : Fin κ,
        Measurable
          (MeasurableEquiv.finTwoArrow :
            (Fin 2 → ℝ) → ℝ × ℝ) :=
    fun _ =>
      MeasurableEquiv.finTwoArrow.measurable
  -- `finTwoArrow` sends the function-valued Gaussian mark law to the product Gaussian law.
  have hmap :
      coordinateMapLaw
        (siteGaussianMarks (Fin 2) κ vs)
        (fun _ => MeasurableEquiv.finTwoArrow)
        hArrow
        =
      fun p =>
        (gaussianReal 0 (vs p)).prod
          (gaussianReal 0 (vs p)) := by
    funext p
    change
      (siteGaussianMarks (Fin 2) κ vs p).map
          MeasurableEquiv.finTwoArrow
        =
      (gaussianReal 0 (vs p)).prod
        (gaussianReal 0 (vs p))
    exact
      (measurePreserving_finTwoArrow
        (gaussianReal 0 (vs p))).map_eq
  calc
    cascadeTilt κ
        (halveBelow (τ - 1) ms)
        (siteGaussianMarks (Fin 2) κ vs)
        (fun y =>
          ENNReal.ofReal
            (Real.exp
              (pairSiteF 0 (fun _ => h)
                (couplingFactorSgn 1 τ 0)
                (fun p =>
                  couplingFactorSgn 1 τ
                    (p.val + 1))
                y₀ y)))
        (fun y =>
          ENNReal.ofReal
            (Real.tanh
              (h +
                pairSiteMark
                  (couplingFactorSgn 1 τ 0)
                  (fun p =>
                    couplingFactorSgn 1 τ
                      (p.val + 1))
                  y₀ y 0)
              + c)
            *
          ENNReal.ofReal
            (Real.tanh
              (h +
                pairSiteMark
                  (couplingFactorSgn 1 τ 0)
                  (fun p =>
                    couplingFactorSgn 1 τ
                      (p.val + 1))
                  y₀ y 1)
              + c))
        =
      cascadeTilt κ
        (halveBelow (τ - 1) ms)
        (coordinateMapLaw
          (siteGaussianMarks (Fin 2) κ vs)
          (fun _ =>
            MeasurableEquiv.finTwoArrow)
          hArrow)
        Ĝ Â := by
          rw [hF, hObs]
          symm
          exact
            cascadeTilt_coordinateMap
              (T := Fin 2 → ℝ)
              (T' := ℝ × ℝ)
              κ
              (halveBelow (τ - 1) ms)
              (siteGaussianMarks (Fin 2) κ vs)
              (fun _ =>
                MeasurableEquiv.finTwoArrow)
              hArrow hĜ hÂ
    _ =
      cascadeTilt κ
        (halveBelow (τ - 1) ms)
        (fun p =>
          (gaussianReal 0 (vs p)).prod
            (gaussianReal 0 (vs p)))
        Ĝ Â := by
          exact
            cascadeTilt_congr_measure
              (halveBelow (τ - 1) ms)
              hmap Ĝ Â
    _ =
      cascadeTiltSq κ (τ - 1) ms
        (fun p => gaussianReal 0 (vs p))
        G A := by
          simpa [Ĝ, Â] using
            (cascadeTilt_coupling_prod
              κ (τ - 1) ms
              (fun p => gaussianReal 0 (vs p))
              hG hA hGpos hpos)
    _ =
      cascadeTiltSq κ (τ - 1) ms
        (fun p => gaussianReal 0 (vs p))
        (logCoshWeight (κ := κ) (h + y₀ 0))
        (shiftedTanhWeight (κ := κ) c
          (h + y₀ 0)) := by
          rfl

/-- Convert the real integral of the nonnegative shifted product to the corresponding
`ℝ≥0∞`-valued tilted square, and then apply `ENNReal.toReal`. -/
private lemma integral_pairSiteTanh_shift_eq_cascadeTiltSq
    (ms : Fin κ → ℝ)
    (hpos : ∀ i, 0 < ms i)
    (vs : Fin κ → ℝ≥0)
    (h : ℝ)
    (y₀ : Fin 2 → ℝ)
    {τ : ℕ}
    (hτ : 1 ≤ τ)
    (c : ℝ)
    (hc : 1 ≤ c) :
    let μ :=
      cascadeTiltMeasure κ
        (halveBelow (τ - 1) ms)
        (siteGaussianMarks (Fin 2) κ vs)
        (fun y =>
          ENNReal.ofReal
            (Real.exp
              (pairSiteF 0 (fun _ => h)
                (couplingFactorSgn 1 τ 0)
                (fun p =>
                  couplingFactorSgn 1 τ
                    (p.val + 1))
                y₀ y)))
    ∫ y,
        (Real.tanh
            (h +
              pairSiteMark
                (couplingFactorSgn 1 τ 0)
                (fun p =>
                  couplingFactorSgn 1 τ
                    (p.val + 1))
                y₀ y 0)
          + c)
        *
        (Real.tanh
            (h +
              pairSiteMark
                (couplingFactorSgn 1 τ 0)
                (fun p =>
                  couplingFactorSgn 1 τ
                    (p.val + 1))
                y₀ y 1)
          + c)
      ∂μ
      =
    (cascadeTiltSq κ (τ - 1) ms
      (fun p => gaussianReal 0 (vs p))
      (logCoshWeight (κ := κ) (h + y₀ 0))
      (shiftedTanhWeight (κ := κ) c
        (h + y₀ 0))).toReal := by
  dsimp only
  let t₀ :
      (Fin κ → Fin 2 → ℝ) → ℝ :=
    fun y =>
      Real.tanh
        (h +
          pairSiteMark
            (couplingFactorSgn 1 τ 0)
            (fun p =>
              couplingFactorSgn 1 τ
                (p.val + 1))
            y₀ y 0)
  let t₁ :
      (Fin κ → Fin 2 → ℝ) → ℝ :=
    fun y =>
      Real.tanh
        (h +
          pairSiteMark
            (couplingFactorSgn 1 τ 0)
            (fun p =>
              couplingFactorSgn 1 τ
                (p.val + 1))
            y₀ y 1)
  let S :
      (Fin κ → Fin 2 → ℝ) → ℝ :=
    fun y => (t₀ y + c) * (t₁ y + c)
  have ht₀c : Continuous t₀ := continuous_pairSiteTanhField_coupling h y₀ τ 0
  have ht₁c : Continuous t₁ := continuous_pairSiteTanhField_coupling h y₀ τ 1
  have hSm : Measurable S :=
    ((ht₀c.add continuous_const).mul
      (ht₁c.add continuous_const)).measurable
  have hSnonneg :
      ∀ y, 0 ≤ S y := by
    intro y
    dsimp [S]
    apply mul_nonneg
    · dsimp [t₀]
      linarith [Real.neg_one_lt_tanh
        (h +
          pairSiteMark
            (couplingFactorSgn 1 τ 0)
            (fun p =>
              couplingFactorSgn 1 τ
                (p.val + 1))
            y₀ y 0)]
    · dsimp [t₁]
      linarith [Real.neg_one_lt_tanh
        (h +
          pairSiteMark
            (couplingFactorSgn 1 τ 0)
            (fun p =>
              couplingFactorSgn 1 τ
                (p.val + 1))
            y₀ y 1)]
  have hGm :
      Measurable fun y :
          Fin κ → Fin 2 → ℝ =>
        ENNReal.ofReal
          (Real.exp
            (pairSiteF 0 (fun _ => h)
              (couplingFactorSgn 1 τ 0)
              (fun p =>
                couplingFactorSgn 1 τ
                  (p.val + 1))
              y₀ y)) := by
    exact
      ENNReal.measurable_ofReal.comp
        (Real.measurable_exp.comp
          (measurable_pairSiteF' 0
            (fun _ => h)
            (couplingFactorSgn 1 τ 0)
            (fun p =>
              couplingFactorSgn 1 τ
                (p.val + 1))
            y₀))
  have hSenn :
      Measurable fun y =>
        ENNReal.ofReal (S y) :=
    ENNReal.measurable_ofReal.comp hSm
  have hofReal :
      (fun y =>
        ENNReal.ofReal (S y))
        =
      fun y =>
        ENNReal.ofReal (t₀ y + c)
          *
        ENNReal.ofReal (t₁ y + c) := by
    funext y
    dsimp [S]
    rw [ENNReal.ofReal_mul]
    dsimp [t₀]
    linarith [Real.neg_one_lt_tanh
      (h +
        pairSiteMark
          (couplingFactorSgn 1 τ 0)
          (fun p =>
            couplingFactorSgn 1 τ
              (p.val + 1))
          y₀ y 0)]
  -- The nonnegativity of the shift permits passage from the Bochner integral to `lintegral`.
  rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall hSnonneg)
      hSm.aestronglyMeasurable]
  rw [lintegral_cascadeTiltMeasure
      κ
      (halveBelow (τ - 1) ms)
      (siteGaussianMarks (Fin 2) κ vs)
      hGm hSenn]
  rw [hofReal]
  exact congrArg ENNReal.toReal
    (cascadeTilt_pairSite_zero_shift
      ms hpos vs h y₀ hτ c)

/-- At a fixed root pair, the integral of the terminal derivative is Talagrand's signed
conditional square.  The proof applies the shift identity pointwise, integrates it, and replaces
the two shifted integrals by the preceding tilted-square formula. -/
private lemma integral_pairSiteF'_coupling_zero
    (ms : Fin κ → ℝ)
    (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1)
    (vs : Fin κ → ℝ≥0)
    (h : ℝ)
    (y₀ : Fin 2 → ℝ)
    {τ : ℕ}
    (hτ : 1 ≤ τ) :
    ∫ y,
      pairSiteF' 0 (fun _ => h)
        (couplingFactorSgn 1 τ 0)
        (fun p =>
          couplingFactorSgn 1 τ
            (p.val + 1))
        y₀ y
      ∂cascadeTiltMeasure κ
        (halveBelow (τ - 1) ms)
        (siteGaussianMarks (Fin 2) κ vs)
        (fun y =>
          ENNReal.ofReal
            (Real.exp
              (pairSiteF 0 (fun _ => h)
                (couplingFactorSgn 1 τ 0)
                (fun p =>
                  couplingFactorSgn 1 τ
                    (p.val + 1))
                y₀ y)))
      =
    cascadeTiltTanhSq ms vs
      (τ - 1) (h + y₀ 0) := by
  let μ :=
    cascadeTiltMeasure κ
      (halveBelow (τ - 1) ms)
      (siteGaussianMarks (Fin 2) κ vs)
      (fun y =>
        ENNReal.ofReal
          (Real.exp
            (pairSiteF 0 (fun _ => h)
              (couplingFactorSgn 1 τ 0)
              (fun p =>
                couplingFactorSgn 1 τ
                  (p.val + 1))
              y₀ y)))
  let t₀ :
      (Fin κ → Fin 2 → ℝ) → ℝ :=
    fun y =>
      Real.tanh
        (h +
          pairSiteMark
            (couplingFactorSgn 1 τ 0)
            (fun p =>
              couplingFactorSgn 1 τ
                (p.val + 1))
            y₀ y 0)
  let t₁ :
      (Fin κ → Fin 2 → ℝ) → ℝ :=
    fun y =>
      Real.tanh
        (h +
          pairSiteMark
            (couplingFactorSgn 1 τ 0)
            (fun p =>
              couplingFactorSgn 1 τ
                (p.val + 1))
            y₀ y 1)
  let S₁ :
      (Fin κ → Fin 2 → ℝ) → ℝ :=
    fun y =>
      (t₀ y + 1) * (t₁ y + 1)
  let S₂ :
      (Fin κ → Fin 2 → ℝ) → ℝ :=
    fun y =>
      (t₀ y + 2) * (t₁ y + 2)
  -- This normalization is what turns the integral of the final constant `2` into `2`.
  let _ : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact isProbabilityMeasure_cascadeTiltMeasure_pairSiteF
      (halveBelow (τ - 1) ms) (fun i => halveBelow_pos hpos _ i)
      (fun i => halveBelow_le_one hle _ i) vs 0 (fun _ => h)
      (couplingFactorSgn 1 τ 0)
      (fun p => couplingFactorSgn 1 τ (p.val + 1)) y₀
  have ht₀c : Continuous t₀ := continuous_pairSiteTanhField_coupling h y₀ τ 0
  have ht₁c : Continuous t₁ := continuous_pairSiteTanhField_coupling h y₀ τ 1
  have ht₀lower (y) : -1 < t₀ y := by
    dsimp [t₀]
    exact Real.neg_one_lt_tanh _
  have ht₀upper (y) : t₀ y < 1 := by
    dsimp [t₀]
    exact Real.tanh_lt_one _
  have ht₁lower (y) : -1 < t₁ y := by
    dsimp [t₁]
    exact Real.neg_one_lt_tanh _
  have ht₁upper (y) : t₁ y < 1 := by
    dsimp [t₁]
    exact Real.tanh_lt_one _
  have hS₁i : Integrable S₁ μ := by
    simpa [S₁] using integrable_shift_mul_of_mem_Ioo μ t₀ t₁ ht₀c.measurable ht₁c.measurable
      ht₀lower ht₀upper ht₁lower ht₁upper 1 (by norm_num)
  have hS₂i : Integrable S₂ μ := by
    simpa [S₂] using integrable_shift_mul_of_mem_Ioo μ t₀ t₁ ht₀c.measurable ht₁c.measurable
      ht₀lower ht₀upper ht₁lower ht₁upper 2 (by norm_num)
  have hshift₁ :
      ∫ y, S₁ y ∂μ
        =
      (cascadeTiltSq κ (τ - 1) ms
        (fun p => gaussianReal 0 (vs p))
        (logCoshWeight (κ := κ) (h + y₀ 0))
        (shiftedTanhWeight (κ := κ) 1
          (h + y₀ 0))).toReal := by
    simpa [μ, S₁, t₀, t₁] using
      (integral_pairSiteTanh_shift_eq_cascadeTiltSq
        ms hpos vs h y₀ hτ
        1 (by norm_num))
  have hshift₂ :
      ∫ y, S₂ y ∂μ
        =
      (cascadeTiltSq κ (τ - 1) ms
        (fun p => gaussianReal 0 (vs p))
        (logCoshWeight (κ := κ) (h + y₀ 0))
        (shiftedTanhWeight (κ := κ) 2
          (h + y₀ 0))).toReal := by
    simpa [μ, S₂, t₀, t₁] using
      (integral_pairSiteTanh_shift_eq_cascadeTiltSq
        ms hpos vs h y₀ hτ
        2 (by norm_num))
  -- Recover the signed product from its two nonnegative shifts.
  have hpoint :
      ∀ y,
        pairSiteF' 0 (fun _ => h)
          (couplingFactorSgn 1 τ 0)
          (fun p =>
            couplingFactorSgn 1 τ
              (p.val + 1))
          y₀ y
        =
        2 * S₁ y - S₂ y + 2 := by
    intro y
    rw [pairSiteF'_zero]
    dsimp [S₁, S₂, t₀, t₁]
    ring
  change
    (∫ y,
      pairSiteF' 0 (fun _ => h)
        (couplingFactorSgn 1 τ 0)
        (fun p =>
          couplingFactorSgn 1 τ
            (p.val + 1))
        y₀ y ∂μ)
      =
    cascadeTiltTanhSq ms vs
      (τ - 1) (h + y₀ 0)
  calc
    ∫ y,
        pairSiteF' 0 (fun _ => h)
          (couplingFactorSgn 1 τ 0)
          (fun p =>
            couplingFactorSgn 1 τ
              (p.val + 1))
          y₀ y ∂μ
        =
      ∫ y,
        (2 * S₁ y - S₂ y + 2) ∂μ := by
          exact integral_congr_ae
            (Filter.Eventually.of_forall hpoint)
    _ =
      2 * (∫ y, S₁ y ∂μ)
        - (∫ y, S₂ y ∂μ) + 2 := by
          calc
            ∫ y, 2 * S₁ y - S₂ y + 2 ∂μ =
                (∫ y, 2 * S₁ y - S₂ y ∂μ) + ∫ _y, 2 ∂μ :=
              integral_add ((hS₁i.const_mul 2).sub hS₂i) (integrable_const 2)
            _ = 2 * (∫ y, S₁ y ∂μ) - (∫ y, S₂ y ∂μ) + 2 := by
              rw [integral_sub (hS₁i.const_mul 2) hS₂i,
                integral_const_mul, integral_const]
              simp
    _ =
      cascadeTiltTanhSq ms vs
        (τ - 1) (h + y₀ 0) := by
          rw [hshift₁, hshift₂]
          rfl

/-!
### Proposition 14.6.4(a): equations (14.176) and (14.177)

Equation (14.176) is `pairSiteY₀_coupling_zero` from `CoupledLambdaZero`.  For (14.177), the
fixed-root identity is integrated over the two-dimensional root mark and then projected to its
shared first coordinate.  The differentiability statement is recorded before the final
conjunction.  The equality of the marks below `τ` is encoded by `couplingFactorSgn 1 τ` and
`couplingMap (τ - 1)` rather than imposed as an additional hypothesis.
-/

/-- The fixed-root form of Talagrand's (14.177), before projecting the root pair to the shared
coordinate `y₀ 0`.  The common marks below `τ` are built into `couplingFactorSgn 1 τ`. -/
private theorem pairSiteY₀'_coupling_zero_pi
    (ms : Fin κ → ℝ)
    (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1)
    (v₀ : ℝ≥0)
    (vs : Fin κ → ℝ≥0)
    (h : ℝ)
    {τ : ℕ}
    (hτ : 1 ≤ τ) :
    pairSiteY₀'
        (J := Fin 2)
        (halveBelow (τ - 1) ms)
        v₀ vs 0
        (fun _ => h)
        (couplingFactorSgn 1 τ 0)
        (fun p =>
          couplingFactorSgn 1 τ
            (p.val + 1))
      =
    ∫ y₀,
      cascadeTiltTanhSq
        ms vs (τ - 1)
        (h + y₀ 0)
      ∂Measure.pi
        fun _ : Fin 2 =>
          gaussianReal 0 v₀ := by
  unfold pairSiteY₀'
  exact integral_congr_ae <| Filter.Eventually.of_forall fun y₀ =>
    integral_pairSiteF'_coupling_zero ms hpos hle vs h y₀ hτ

/-- Talagrand, Proposition 14.6.4(a), equation (14.177): the derivative at zero is the
one-dimensional Gaussian average of the signed, prefix-weighted conditional square.  The
condition that the two copies share their marks below `τ` is encoded by `couplingFactorSgn 1 τ`;
the unused root coordinate disappears by pushing the product root law forward through evaluation
at `0`. -/
theorem pairSiteY₀'_coupling_zero
    (ms : Fin κ → ℝ)
    (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1)
    (v₀ : ℝ≥0)
    (vs : Fin κ → ℝ≥0)
    (h : ℝ)
    {τ : ℕ}
    (hτ : 1 ≤ τ) :
    pairSiteY₀'
        (J := Fin 2)
        (halveBelow (τ - 1) ms)
        v₀ vs 0
        (fun _ => h)
        (couplingFactorSgn 1 τ 0)
        (fun p => couplingFactorSgn 1 τ (p.val + 1))
      =
    ∫ a,
      cascadeTiltTanhSq ms vs (τ - 1) (h + a)
      ∂gaussianReal 0 v₀ := by
  rw [pairSiteY₀'_coupling_zero_pi ms hpos hle v₀ vs h hτ]
  have hm : Measurable fun a : ℝ =>
      cascadeTiltTanhSq ms vs (τ - 1) (h + a) :=
    (measurable_cascadeTiltTanhSq ms vs (τ - 1)).comp
      (measurable_const.add measurable_id)
  have hme :
      (Measure.pi fun _ : Fin 2 => gaussianReal 0 v₀).map (fun y₀ => y₀ 0)
        = gaussianReal 0 v₀ :=
    (measurePreserving_eval _ 0).map_eq
  conv_rhs => rw [← hme]
  rw [integral_map (measurable_pi_apply 0).aemeasurable hm.aestronglyMeasurable]

/-- The coupled site functional is differentiable at zero, with derivative given by Talagrand's
Proposition 14.6.4(a), equation (14.177). -/
theorem hasDerivAt_pairSiteY₀_coupling_zero
    (ms : Fin κ → ℝ)
    (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1)
    (v₀ : ℝ≥0)
    (vs : Fin κ → ℝ≥0)
    (h : ℝ)
    {τ : ℕ}
    (hτ : 1 ≤ τ) :
    HasDerivAt
      (fun lam =>
        pairSiteY₀
          (J := Fin 2)
          (halveBelow (τ - 1) ms)
          v₀ vs lam
          (fun _ => h)
          (couplingFactorSgn 1 τ 0)
          (fun p =>
            couplingFactorSgn 1 τ
              (p.val + 1)))
      (∫ a,
        cascadeTiltTanhSq ms vs (τ - 1) (h + a)
        ∂gaussianReal 0 v₀)
      0 := by
  rw [← pairSiteY₀'_coupling_zero ms hpos hle v₀ vs h hτ]
  exact hasDerivAt_pairSiteY₀ (J' := Fin 2) (halveBelow (τ - 1) ms)
    (fun i => halveBelow_pos hpos _ i) (fun i => halveBelow_le_one hle _ i)
    v₀ vs 0 (fun _ => h) (couplingFactorSgn 1 τ 0)
    (fun p => couplingFactorSgn 1 τ (p.val + 1))

/-- Talagrand, Proposition 14.6.4(a), equations (14.176) and (14.177).
For the coupling at level `τ ≥ 1` with `η = 1` and exponents
`n_p = m_p / 2` below `τ` and `n_p = m_p` from `τ` onward,

(14.176) `Y₀(0) = 2 X₀`;

(14.177) `Y₀'(0) = 𝔼(W₁ ⋯ W_{τ-1} D'_τ(ζ_τ)^2)`.

The shared-mark condition below `τ` is encoded structurally by `couplingFactorSgn 1 τ` and does
not appear as a separate theorem hypothesis.
-/
theorem pairSiteY₀_coupling_zero_and_deriv
    (ms : Fin κ → ℝ)
    (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1)
    (v₀ : ℝ≥0)
    (vs : Fin κ → ℝ≥0)
    (h : ℝ)
    {τ : ℕ}
    (hτ : 1 ≤ τ) :
    pairSiteY₀
        (J := Fin 2)
        (halveBelow (τ - 1) ms)
        v₀ vs 0
        (fun _ => h)
        (couplingFactorSgn 1 τ 0)
        (fun p => couplingFactorSgn 1 τ (p.val + 1))
      =
        2 * ∫ a, logCoshRec κ ms vs (h + a)
          ∂gaussianReal 0 v₀
    ∧
    pairSiteY₀'
        (J := Fin 2)
        (halveBelow (τ - 1) ms)
        v₀ vs 0
        (fun _ => h)
        (couplingFactorSgn 1 τ 0)
        (fun p => couplingFactorSgn 1 τ (p.val + 1))
      =
        ∫ a,
          cascadeTiltTanhSq ms vs (τ - 1) (h + a)
          ∂gaussianReal 0 v₀ := by
  exact ⟨pairSiteY₀_coupling_zero ms hpos v₀ vs h hτ,
    pairSiteY₀'_coupling_zero ms hpos hle v₀ vs h hτ⟩

end

end SpinGlass
