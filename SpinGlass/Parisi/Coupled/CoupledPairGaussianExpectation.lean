import SpinGlass.Parisi.Coupled.CoupledPairGaussianRecursion

/-!
# The finite product expectation of zero-mass paired roots

Separately unit-Lipschitz terminals have an integrable linear bound under
the actual finite Gaussian product. Fubini therefore identifies successive
mass-zero paired operators with the joint root expectation. No zero mass
is supplied to the positive-mass cascade recursion.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

@[fun_prop] theorem continuous_pairGaussianShift (kind : PairColeHopfKind) :
    Continuous (pairGaussianShift kind) := by
  cases kind <;> unfold pairGaussianShift <;> fun_prop

theorem abs_pairGaussianShift_fst_le (kind : PairColeHopfKind) (z : Fin 2 → ℝ) :
    |(pairGaussianShift kind z).1| ≤ |z 0| + |z 1| := by
  cases kind <;> simp only [pairGaussianShift] <;> linarith [abs_nonneg (z 1)]

theorem abs_pairGaussianShift_snd_le (kind : PairColeHopfKind) (z : Fin 2 → ℝ) :
    |(pairGaussianShift kind z).2| ≤ |z 0| + |z 1| := by
  cases kind <;> simp only [pairGaussianShift, abs_neg] <;>
    linarith [abs_nonneg (z 0), abs_nonneg (z 1)]

theorem integrable_abs_gaussianReal_zero (v : ℝ≥0) :
    Integrable (fun z : ℝ => |z|) (gaussianReal 0 v) := by
  have hg : HasLinearGrowth (fun z : ℝ => |z|) :=
    ⟨0, 1, by norm_num, fun z => by simp⟩
  have hm : Measurable (fun z : ℝ => |z|) := by fun_prop
  exact hg.toHasExpGrowth.integrable_gaussianReal hm.aestronglyMeasurable

theorem integrable_abs_pairGaussianMarks_apply {k : ℕ}
    (vs : Fin k → ℝ≥0) (i : Fin k) (j : Fin 2) :
    Integrable (fun zs : Fin k → Fin 2 → ℝ => |zs i j|)
      (Measure.pi (siteGaussianMarks (Fin 2) k vs)) := by
  have hscalar := integrable_abs_gaussianReal_zero (vs i)
  have hm : Measurable (fun z : ℝ => |z|) := by fun_prop
  have hinner : Integrable (fun z : Fin 2 → ℝ => |z j|)
      (siteGaussianMarks (Fin 2) k vs i) :=
    ((measurePreserving_eval (μ := fun _ : Fin 2 => gaussianReal 0 (vs i)) j).integrable_comp
      hm.aestronglyMeasurable).2 hscalar
  exact ((measurePreserving_eval (μ := siteGaussianMarks (Fin 2) k vs) i).integrable_comp
    hinner.aestronglyMeasurable).2 hinner

/-- A concrete finite sum of all actual paired root marks has an
integrable terminal, even when some variances are zero. -/
theorem integrable_pairGaussian_comp_add_sum {k : ℕ}
    (ps : Fin k → PairColeHopfLevel) {F : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (x y : ℝ) :
    Integrable (fun zs : Fin k → Fin 2 → ℝ =>
      F (x + ∑ i, (pairGaussianShift (ps i).kind (zs i)).1)
        (y + ∑ i, (pairGaussianShift (ps i).kind (zs i)).2))
      (Measure.pi (siteGaussianMarks (Fin 2) k (fun i => (ps i).variance))) := by
  have hmeas : Measurable (fun zs : Fin k → Fin 2 → ℝ =>
      F (x + ∑ i, (pairGaussianShift (ps i).kind (zs i)).1)
        (y + ∑ i, (pairGaussianShift (ps i).kind (zs i)).2)) :=
    (hF.continuous_uncurry.comp
      (show Continuous (fun zs : Fin k → Fin 2 → ℝ =>
        (x + ∑ i, (pairGaussianShift (ps i).kind (zs i)).1,
          y + ∑ i, (pairGaussianShift (ps i).kind (zs i)).2)) by fun_prop)).measurable
  have hsum : Integrable (fun zs : Fin k → Fin 2 → ℝ => ∑ i, (|zs i 0| + |zs i 1|))
      (Measure.pi (siteGaussianMarks (Fin 2) k (fun i => (ps i).variance))) :=
    integrable_finsetSum _ fun i _ =>
      (integrable_abs_pairGaussianMarks_apply _ i 0).add
        (integrable_abs_pairGaussianMarks_apply _ i 1)
  apply ((integrable_const |F x y|).add (hsum.const_mul 2)).mono'
    hmeas.aestronglyMeasurable
  filter_upwards [] with zs
  rw [Real.norm_eq_abs]
  let sx := ∑ i, (pairGaussianShift (ps i).kind (zs i)).1
  let sy := ∑ i, (pairGaussianShift (ps i).kind (zs i)).2
  have hx : |sx| ≤ ∑ i, (|zs i 0| + |zs i 1|) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => abs_pairGaussianShift_fst_le (ps i).kind (zs i))
  have hy : |sy| ≤ ∑ i, (|zs i 0| + |zs i 1|) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => abs_pairGaussianShift_snd_le (ps i).kind (zs i))
  have hdiff := hF x y (x + sx) (y + sy)
  simp only [add_sub_cancel_left] at hdiff
  have htri : |F (x + sx) (y + sy)| ≤ |F x y| + |F (x + sx) (y + sy) - F x y| := by
    calc
      _ = |F x y + (F (x + sx) (y + sy) - F x y)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  change |F (x + sx) (y + sy)| ≤ |F x y| + 2 * ∑ i, (|zs i 0| + |zs i 1|)
  calc
    _ ≤ |F x y| + |F (x + sx) (y + sy) - F x y| := htri
    _ ≤ |F x y| + (|sx| + |sy|) := add_le_add le_rfl hdiff
    _ ≤ |F x y| + ((∑ i, (|zs i 0| + |zs i 1|)) + ∑ i, (|zs i 0| + |zs i 1|)) :=
      add_le_add le_rfl (add_le_add hx hy)
    _ = _ := by ring

/-- The joint product expectation of all zero-mass paired Gaussian
roots is the actual paired root iterate, with Fubini justified above. -/
theorem integral_pairGaussian_comp_add_sum_mass_zero (k : ℕ) :
    ∀ (ps : Fin k → PairColeHopfLevel), (∀ i, (ps i).mass = 0) →
      ∀ {F : ℝ → ℝ → ℝ}, PairUnitLipschitz F → ∀ x y : ℝ,
    (∫ zs : Fin k → Fin 2 → ℝ,
      F (x + ∑ i, (pairGaussianShift (ps i).kind (zs i)).1)
        (y + ∑ i, (pairGaussianShift (ps i).kind (zs i)).2)
      ∂Measure.pi (siteGaussianMarks (Fin 2) k (fun i => (ps i).variance))) =
      pairColeHopfIterate (List.ofFn ps) F x y := by
  induction k with
  | zero =>
    intro ps _ F _ x y
    simp [pairColeHopfIterate]
  | succ k ih =>
    intro ps hzero F hF x y
    let A := pairColeHopfIterate (List.ofFn (Fin.tail ps)) F
    have hA : PairUnitLipschitz A := pairColeHopfIterate_lipschitz _ hF
    have hμ : Fin.tail (siteGaussianMarks (Fin 2) (k + 1) (fun i => (ps i).variance)) =
        siteGaussianMarks (Fin 2) k (fun i => (ps i.succ).variance) := by
      funext i
      rfl
    have hinner (z : Fin 2 → ℝ) :
        (∫ zs : Fin k → Fin 2 → ℝ,
          F (x + ∑ i : Fin (k + 1), (pairGaussianShift (ps i).kind
              ((Fin.cons z zs : Fin (k + 1) → Fin 2 → ℝ) i)).1)
            (y + ∑ i : Fin (k + 1), (pairGaussianShift (ps i).kind
              ((Fin.cons z zs : Fin (k + 1) → Fin 2 → ℝ) i)).2)
          ∂Measure.pi (Fin.tail (siteGaussianMarks (Fin 2) (k + 1) (fun i => (ps i).variance)))) =
          A (x + (pairGaussianShift (ps 0).kind z).1)
            (y + (pairGaussianShift (ps 0).kind z).2) := by
      rw [hμ]
      have hh := ih (Fin.tail ps) (fun i => hzero i.succ) hF
        (x + (pairGaussianShift (ps 0).kind z).1)
        (y + (pairGaussianShift (ps 0).kind z).2)
      simpa only [Fin.tail, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        add_assoc, A] using hh
    rw [integral_pi_fin_succ _ (integrable_pairGaussian_comp_add_sum ps hF x y)]
    simp only [hinner]
    change (∫ z : Fin 2 → ℝ, A (x + (pairGaussianShift (ps 0).kind z).1)
      (y + (pairGaussianShift (ps 0).kind z).2)
      ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 (ps 0).variance)) = _
    rw [← pairColeHopfOperator_zero_eq_gaussian_integral hA (ps 0) (hzero 0) x y,
      List.ofFn_succ]
    rfl

theorem pairColeHopfIterate_append (pre tail : List PairColeHopfLevel) (F : ℝ → ℝ → ℝ) :
    pairColeHopfIterate (pre ++ tail) F = pairColeHopfIterate pre (pairColeHopfIterate tail F) := by
  induction pre with
  | nil => rfl
  | cons p pre ih => simp only [List.cons_append, pairColeHopfIterate, ih]

theorem map_pi_pairGaussianMarks_curry {k : ℕ} (vs : Fin k → ℝ≥0) :
    (Measure.pi (fun j : Fin k × Fin 2 => gaussianReal 0 (vs j.1))).map
        (MeasurableEquiv.curry (Fin k) (Fin 2) ℝ) =
      Measure.pi (siteGaussianMarks (Fin 2) k vs) := by
  change (Measure.pi (fun j : Fin k × Fin 2 => gaussianReal 0 (vs j.1))).map
      (MeasurableEquiv.curry (Fin k) (Fin 2) ℝ) =
    Measure.pi (fun i : Fin k => Measure.pi (fun _ : Fin 2 => gaussianReal 0 (vs i)))
  simpa only [Measure.infinitePi_eq_pi] using
    Measure.infinitePi_map_curry (fun i : Fin k => fun _ : Fin 2 => gaussianReal 0 (vs i))

/-- Flattened actual Gaussian root coordinates give the same
mass-zero paired iterate as the nested product law. -/
theorem integral_pairGaussian_flat_comp_add_sum_mass_zero {k : ℕ}
    (ps : Fin k → PairColeHopfLevel) (hzero : ∀ i, (ps i).mass = 0)
    {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) (x y : ℝ) :
    (∫ z : Fin k × Fin 2 → ℝ,
      F (x + ∑ j, (ps j.1).kind.gaussianFactor 0 j.2 * z j)
        (y + ∑ j, (ps j.1).kind.gaussianFactor 1 j.2 * z j)
      ∂Measure.pi (fun j : Fin k × Fin 2 => gaussianReal 0 (ps j.1).variance)) =
      pairColeHopfIterate (List.ofFn ps) F x y := by
  let f (zs : Fin k → Fin 2 → ℝ) :=
    F (x + ∑ i, (pairGaussianShift (ps i).kind (zs i)).1)
      (y + ∑ i, (pairGaussianShift (ps i).kind (zs i)).2)
  have hmp : MeasurePreserving (MeasurableEquiv.curry (Fin k) (Fin 2) ℝ)
      (Measure.pi (fun j : Fin k × Fin 2 => gaussianReal 0 (ps j.1).variance))
      (Measure.pi (siteGaussianMarks (Fin 2) k (fun i => (ps i).variance))) :=
    ⟨(MeasurableEquiv.curry (Fin k) (Fin 2) ℝ).measurable,
      map_pi_pairGaussianMarks_curry (fun i : Fin k => (ps i).variance)⟩
  have he := hmp.integral_comp' f
  change (∫ z : Fin k × Fin 2 → ℝ, f ((MeasurableEquiv.curry (Fin k) (Fin 2) ℝ) z)
      ∂Measure.pi (fun j : Fin k × Fin 2 => gaussianReal 0 (ps j.1).variance)) =
    (∫ zs : Fin k → Fin 2 → ℝ, F (x + ∑ i, (pairGaussianShift (ps i).kind (zs i)).1)
      (y + ∑ i, (pairGaussianShift (ps i).kind (zs i)).2)
      ∂Measure.pi (siteGaussianMarks (Fin 2) k (fun i => (ps i).variance))) at he
  rw [integral_pairGaussian_comp_add_sum_mass_zero k ps hzero hF x y] at he
  simpa only [f, MeasurableEquiv.coe_curry, Function.curry,
    pairGaussianShift_eq_factor, Fintype.sum_prod_type] using he

end SpinGlass
