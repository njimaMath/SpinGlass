import SpinGlass.Parisi.Variational.ParisiMassPropagation
import SpinGlass.Parisi.Variational.ParisiVarianceResponse

/-!
# Signed Gaussian cascade transport

Integrating out the last mark transports a bounded observable through its
actual normalized Cole-Hopf weight. This identifies the extra prefix weight
in the outer U endpoint with the local q-moment in (14.219).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

private theorem integral_pi_fin_snoc {n : ℕ} (μs : Fin (n + 1) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μs i)] {g : (Fin (n + 1) → ℝ) → ℝ}
    (hg : Integrable g (Measure.pi μs)) :
    (∫ zs, g zs ∂Measure.pi μs) =
      ∫ zs, ∫ z, g (Fin.snoc zs z) ∂μs (Fin.last n)
        ∂Measure.pi (fun i => μs i.castSucc) := by
  have hmp := (measurePreserving_piFinSuccAbove μs (Fin.last n)).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n))
  have hge : Integrable (fun q : ℝ × (Fin n → ℝ) =>
      g ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm q))
      ((μs (Fin.last n)).prod (Measure.pi fun i => μs ((Fin.last n).succAbove i))) :=
    (hmp.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ)
        (Fin.last n)).symm.measurableEmbedding).2 hg
  rw [← hmp.integral_comp' g, integral_prod_symm _ hge]
  simp only [Fin.succAbove_last]
  exact integral_congr_ae (.of_forall fun zs => integral_congr_ae (.of_forall fun z => by
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last]
    rfl))

/-- The logarithm of the actual cascade density splits into the preceding
prefix and the last normalized Cole-Hopf weight. -/
theorem coleHopfIterateTiltLog_snoc (j : ℕ) :
    ∀ (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (m : ℝ) (v : ℝ≥0)
      (A : ℝ → ℝ) (x : ℝ) (zs : Fin j → ℝ) (z : ℝ),
      coleHopfIterateTiltLog (j + 1) (Fin.snoc ms m) (Fin.snoc vs v) A x (Fin.snoc zs z) =
        coleHopfIterateTiltLog j ms vs (coleHopf m v A) x zs +
          m * (A (x + ∑ p, zs p + z) - coleHopf m v A (x + ∑ p, zs p)) := by
  induction j with
  | zero =>
    intro ms vs m v A x zs z
    simp [coleHopfIterateTiltLog, Fin.snoc_zero, coleHopfIterate_succ]
  | succ j ih =>
    intro ms vs m v A x zs z
    have hs (f : Fin (j + 1) → ℝ) (c : ℝ) :
        Fin.snoc (α := fun _ => ℝ) f c =
          Fin.cons (f 0) (Fin.snoc (α := fun _ => ℝ) (Fin.tail f) c) := by
      rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
    have hv : Fin.snoc (α := fun _ => ℝ≥0) vs v =
        Fin.cons (vs 0) (Fin.snoc (α := fun _ => ℝ≥0) (Fin.tail vs) v) := by
      rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
    rw [hs ms m, hv, hs zs z]
    conv_lhs => rw [coleHopfIterateTiltLog]
    conv_rhs => rw [coleHopfIterateTiltLog]
    simp only [Fin.cons_zero, Fin.tail_cons]
    rw [coleHopfIterate_snoc_eq, ← hs ms m, ← hv, coleHopfIterate_snoc_eq,
      ih (Fin.tail ms) (Fin.tail vs) m v A (x + zs 0) (Fin.tail zs) z]
    simp only [Fin.sum_univ_succ, Fin.tail, add_assoc]

/-- Integrating the last Gaussian mark of a signed cascade observable gives
exactly its normalized Cole-Hopf transport under the preceding prefix law.
Both the new variance and any prefix variance may be zero. -/
theorem integral_cascadeTiltMeasure_gaussian_snoc {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (v : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ} (hFm : Measurable F) {C : ℝ} (hF : ∀ y, |F y| ≤ C) :
    (∫ zs, F (x + ∑ p, zs p)
      ∂cascadeTiltMeasure (j + 1) (Fin.snoc ms m)
        (fun p => gaussianReal 0 (Fin.snoc (α := fun _ => ℝ≥0) vs v p))
        (fun zs => ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p))))) =
      ∫ zs, (∫ z, F ((x + ∑ p, zs p) + z) *
          coleHopfQ m v A (x + ∑ p, zs p) z ∂gaussianReal 0 v)
        ∂cascadeTiltMeasure j ms (fun p => gaussianReal 0 (vs p))
          (fun zs => ENNReal.ofReal (Real.exp (coleHopf m v A (x + ∑ p, zs p)))) := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  let sms := Fin.snoc (α := fun _ => ℝ) ms m
  let svs := Fin.snoc (α := fun _ => ℝ≥0) vs v
  have hpos' : ∀ p, 0 < sms p := by
    intro p
    refine Fin.lastCases ?_ (fun r => ?_) p
    · simpa only [sms, Fin.snoc_last] using hm
    · simpa only [sms, Fin.snoc_castSucc] using hpos r
  have hle' : ∀ p, sms p ≤ 1 := by
    intro p
    refine Fin.lastCases ?_ (fun r => ?_) p
    · simpa only [sms, Fin.snoc_last] using hm1
    · simpa only [sms, Fin.snoc_castSucc] using hle r
  have hGm : Measurable (fun zs : Fin (j + 1) → ℝ =>
      ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p)))) :=
    ((hAm.comp (measurable_const.add
      (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))).exp.ennreal_ofReal)
  have hGpos : ∀ zs : Fin (j + 1) → ℝ,
      0 < ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p))) :=
    fun _ => ENNReal.ofReal_pos.2 (Real.exp_pos _)
  have hfin := lintegral_ofReal_exp_comp_add_sum_pi_gaussianReal_ne_top svs hL x
  have hobs : Measurable (fun zs : Fin (j + 1) → ℝ => F (x + ∑ p, zs p)) :=
    hFm.comp (measurable_const.add
      (Finset.measurable_sum Finset.univ fun p _ => measurable_pi_apply p))
  have hi := (integrable_toReal_cascadeTiltDensity (j + 1) sms
    (fun p => gaussianReal 0 (svs p)) hGm hGpos hpos' hle' hfin).bdd_mul
    hobs.aestronglyMeasurable (.of_forall fun zs => by
      rw [Real.norm_eq_abs]
      exact hF _)
  have his : Integrable (fun zs : Fin (j + 1) → ℝ =>
      (cascadeTiltDensity (j + 1) sms (fun p => gaussianReal 0 (svs p))
        (fun ys => ENNReal.ofReal (Real.exp (A (x + ∑ p, ys p)))) zs).toReal •
          F (x + ∑ p, zs p)) (Measure.pi (fun p => gaussianReal 0 (svs p))) := by
    simpa only [smul_eq_mul, mul_comm] using hi
  have hB := abs_coleHopf_sub_le_of_lipschitz m hAm hL v
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
  have hBGm : Measurable (fun zs : Fin j → ℝ =>
      ENNReal.ofReal (Real.exp (coleHopf m v A (x + ∑ p, zs p)))) :=
    ((hBm.comp (measurable_const.add
      (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))).exp.ennreal_ofReal)
  rw [integral_cascadeTiltMeasure (j + 1) sms _ hGm hGpos hpos' hle' hfin,
    integral_pi_fin_snoc _ his,
    integral_cascadeTiltMeasure j ms _ hBGm
      (fun zs => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos hle
      (lintegral_ofReal_exp_comp_add_sum_pi_gaussianReal_ne_top vs hB x)]
  simp only [svs, Fin.snoc_last, Fin.snoc_castSucc, smul_eq_mul]
  apply integral_congr_ae
  refine .of_forall fun zs => ?_
  beta_reduce
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine .of_forall fun z => ?_
  beta_reduce
  rw [cascadeTiltDensity_gaussian_eq_exp_tiltLog (j + 1) sms svs hpos' hL,
    cascadeTiltDensity_gaussian_eq_exp_tiltLog j ms vs hpos hB]
  simp only [sms, svs, coleHopfIterateTiltLog_snoc, Fin.sum_snoc, coleHopfQ,
    Real.exp_add, add_assoc]
  ring

end SpinGlass
