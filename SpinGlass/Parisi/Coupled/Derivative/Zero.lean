import SpinGlass.Parisi.Coupled.Derivative.Transport

/-! Identification of the coupled derivative at zero. -/

open MeasureTheory ProbabilityTheory Finset Set Filter Topology
open scoped ENNReal NNReal BigOperators

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

/-- Proposition 14.6.4(a) after averaging the general common i.i.d. site-field law.
The finite first moment supplies integrability at zero coupling. -/
theorem hasDerivAt_randomFieldPairSiteY₀_coupling_zero
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμh : Integrable (fun h : ℝ => h) μh)
    (ms : Fin κ → ℝ) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) {τ : ℕ} (hτ : 1 ≤ τ) :
    HasDerivAt
      (fun lam => randomFieldPairSiteY₀ μh (halveBelow (τ - 1) ms) v₀ vs lam
        (couplingFactorSgn 1 τ 0) (fun p => couplingFactorSgn 1 τ (p.val + 1)))
      (∫ h, ∫ a, cascadeTiltTanhSq ms vs (τ - 1) (h + a) ∂gaussianReal 0 v₀ ∂μh) 0 := by
  have hY : Integrable (fun h : ℝ => pairSiteY₀ (J := Fin 2)
      (halveBelow (τ - 1) ms) v₀ vs 0 (fun _ => h)
      (couplingFactorSgn 1 τ 0) (fun p => couplingFactorSgn 1 τ (p.val + 1))) μh := by
    have hi := (integrable_integral_logCoshRec_externalField hμh ms vs hpos hle v₀).const_mul 2
    refine hi.congr (Filter.Eventually.of_forall fun h => ?_)
    exact (pairSiteY₀_coupling_zero ms hpos v₀ vs h hτ).symm
  have hd := hasDerivAt_randomFieldPairSiteY₀ (μh := μh) (halveBelow (τ - 1) ms)
    (fun i => halveBelow_pos hpos _ i) (fun i => halveBelow_le_one hle _ i)
    v₀ vs 0 (couplingFactorSgn 1 τ 0) (fun p => couplingFactorSgn 1 τ (p.val + 1)) hY
  have heq : randomFieldPairSiteY₀' μh (halveBelow (τ - 1) ms) v₀ vs 0
      (couplingFactorSgn 1 τ 0) (fun p => couplingFactorSgn 1 τ (p.val + 1))
      = ∫ h, ∫ a, cascadeTiltTanhSq ms vs (τ - 1) (h + a) ∂gaussianReal 0 v₀ ∂μh := by
    exact integral_congr_ae (Filter.Eventually.of_forall fun h =>
      pairSiteY₀'_coupling_zero ms hpos hle v₀ vs h hτ)
  rw [heq] at hd
  exact hd

end

end SpinGlass
