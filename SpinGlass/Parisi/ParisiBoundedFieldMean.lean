import SpinGlass.Parisi.Coupled.CoupledOriginalPressure
import SpinGlass.Parisi.Coupled.CoupledFieldPressure
import SpinGlass.Parisi.Analytic.BoundedDifferences
import SpinGlass.Parisi.Analytic.FieldTruncation

/-!
# Fluctuations of the actual conditional mean under clipped site fields

The original physical constrained pressure is a conditional Gaussian
mean. Its coordinate field bound gives a concrete bounded-difference
estimate under the independent clipped site law. This supplies the
field-fluctuation part of the qualification after (14.123); concentration
of the full logarithmic weighted product remains a separate obligation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace SpinGlass

open FiniteGibbs

/-- The original conditional pressure counts each shared site-field
change twice, with a constant independent of the number of levels. -/
theorem abs_parisiAuxPairPressure_shared_field_sub_le {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    (hN : 0 < N) (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (hm : ParisiMAdmissible ms) {t : ℝ} (u : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u)
    (a b : Fin N → ℝ) :
    |parisiAuxPairPressure ξ ms qs (r.val + 1) t u G₀ (sharedReplicaSiteField a) -
      parisiAuxPairPressure ξ ms qs (r.val + 1) t u G₀ (sharedReplicaSiteField b)| ≤
        (2 / (N : ℝ)) * ∑ i, |a i - b i| := by
  have ha := parisiSplitPressure_outer_eq_original hN ξ ms qs r u hm ht G₀
    (sharedReplicaSiteField a) hreach
  have hb := parisiSplitPressure_outer_eq_original hN ξ ms qs r u hm ht G₀
    (sharedReplicaSiteField b) hreach
  have hh := abs_parisiSplitPressure_sub_field_le ξ ms qs r t u hm G₀
    (parisiOuterAuxSplitVars ξ qs r t) hreach (sharedReplicaSiteField a) (sharedReplicaSiteField b)
  rw [ha, hb, add_sub_add_right_eq_sub] at hh
  have hd : replicaSiteFieldDistance (sharedReplicaSiteField a) (sharedReplicaSiteField b) =
      2 * ∑ i, |a i - b i| := by
    simp only [replicaSiteFieldDistance, sharedReplicaSiteField, Fin.sum_univ_two]
    ring
  rw [hd] at hh
  convert hh using 1 <;> ring

/-- The actual conditional mean is continuous in the realized site vector. -/
theorem continuous_parisiAuxPairPressure_shared_field {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    (hN : 0 < N) (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (hm : ParisiMAdmissible ms) {t : ℝ} (u : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    Continuous (fun a : Fin N → ℝ =>
      parisiAuxPairPressure ξ ms qs (r.val + 1) t u G₀ (sharedReplicaSiteField a)) := by
  have hc := (continuous_parisiSplitPressure_siteField ξ ms qs r t u hm G₀
    (parisiOuterAuxSplitVars ξ qs r t) hreach).comp
    (show Continuous (sharedReplicaSiteField (N := N)) from by
      unfold sharedReplicaSiteField
      fun_prop)
  apply (hc.sub (continuous_const (y := (parisiAuxTerminalVar ξ qs t : ℝ)))).congr
  intro a
  have he := parisiSplitPressure_outer_eq_original hN ξ ms qs r u hm ht G₀
    (sharedReplicaSiteField a) hreach
  dsimp only [Function.comp_apply, Pi.sub_apply]
  linarith

/-- The Gaussian conditional mean has an explicit field fluctuation
MGF after coordinatewise clipping. The site law itself needs no
exponential moment; the same clipped coordinate is used in both replicas. -/
theorem integral_exp_parisiAuxPairPressure_clipped_field_mean_le {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    (μh : Measure ℝ) [IsProbabilityMeasure μh]
    (hN : 0 < N) (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (hm : ParisiMAdmissible ms) {t : ℝ} (u : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u)
    {R : ℝ} (hR : 0 ≤ R) (s : ℝ) :
    let F := fun a : Fin N → ℝ => parisiAuxPairPressure ξ ms qs (r.val + 1) t u G₀
      (sharedReplicaSiteField (fun i => Aristotle.clip R (a i)))
    let M := randomFieldParisiAuxPairPressure (μh.map (Aristotle.clip R)) ξ ms qs (r.val + 1) t u G₀
    Integrable (fun a => Real.exp (s * (F a - M))) (externalFieldVecLaw N μh) ∧
      (∫ a, Real.exp (s * (F a - M)) ∂externalFieldVecLaw N μh) ≤
        Real.exp (2 * R ^ 2 * s ^ 2 / N) := by
  classical
  dsimp only
  let P := fun a : Fin N → ℝ => parisiAuxPairPressure ξ ms qs (r.val + 1) t u G₀
    (sharedReplicaSiteField a)
  let C := fun a : Fin N → ℝ => fun i => Aristotle.clip R (a i)
  let F := fun a : Fin N → ℝ => P (C a)
  let c : Fin N → ℝ := fun _ => 4 * R / N
  have hP : Continuous P := continuous_parisiAuxPairPressure_shared_field hN ξ ms qs r hm u ht G₀ hreach
  have hC : Continuous C := by unfold C; fun_prop
  have hF : Measurable F := (hP.comp hC).measurable
  have hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ c i := by
    intro x i y
    have hh := abs_parisiAuxPairPressure_shared_field_sub_le hN ξ ms qs r hm u ht G₀ hreach
      (C (Function.update x i y)) (C x)
    have hsum : (∑ j, |Aristotle.clip R (Function.update x i y j) - Aristotle.clip R (x j)|) =
        |Aristotle.clip R y - Aristotle.clip R (x i)| := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · simp
    have hclip : |Aristotle.clip R y - Aristotle.clip R (x i)| ≤ 2 * R := by
      have hb := abs_sub (Aristotle.clip R y) (Aristotle.clip R (x i))
      linarith [(Aristotle.clip_bounds hR y).1, (Aristotle.clip_bounds hR (x i)).1]
    dsimp only [C] at hh
    rw [hsum] at hh
    have hscale := mul_le_mul_of_nonneg_left hclip (by positivity : 0 ≤ 2 / (N : ℝ))
    have he : 2 / (N : ℝ) * (2 * R) = 4 * R / N := by ring
    rw [he] at hscale
    dsimp only [F, P, C, c]
    exact hh.trans hscale
  have hi : Integrable F (externalFieldVecLaw N μh) :=
    Aristotle.integrable_of_bounded_differences hF hosc measurable_id
  have hb := Aristotle.bounded_differences_mgf (fun _ : Fin N => μh) hF hi c
    (fun i => by dsimp only [c]; positivity) hosc s
  have hmean : (∫ a, F a ∂externalFieldVecLaw N μh) =
      randomFieldParisiAuxPairPressure (μh.map (Aristotle.clip R)) ξ ms qs (r.val + 1) t u G₀ := by
    have htrans := integral_map (μ := externalFieldVecLaw N μh)
      hC.measurable.aemeasurable hP.measurable.aestronglyMeasurable
    have hmap : (externalFieldVecLaw N μh).map C =
        externalFieldVecLaw N (μh.map (Aristotle.clip R)) := Aristotle.map_pi_clip R N
    rw [hmap] at htrans
    exact htrans.symm
  change Integrable (fun a => Real.exp (s * (F a - _))) (externalFieldVecLaw N μh) ∧ _
  rw [← hmean]
  have hvariance : s ^ 2 * (∑ i, c i ^ 2) / 8 = 2 * R ^ 2 * s ^ 2 / N := by
    simp only [c, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    ring
  rw [hvariance] at hb
  exact hb

/-- The concrete clipped-field conditional pressure is sub-Gaussian
around the actual clipped-law average, with parameter 4R²/N. -/
theorem hasSubgaussianMGF_parisiAuxPairPressure_clipped_field_mean {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    (μh : Measure ℝ) [IsProbabilityMeasure μh]
    (hN : 0 < N) (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (hm : ParisiMAdmissible ms) {t : ℝ} (u : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u)
    {R : ℝ} (hR : 0 ≤ R) :
    HasSubgaussianMGF (fun a : Fin N → ℝ =>
      parisiAuxPairPressure ξ ms qs (r.val + 1) t u G₀
        (sharedReplicaSiteField (fun i => Aristotle.clip R (a i))) -
      randomFieldParisiAuxPairPressure (μh.map (Aristotle.clip R)) ξ ms qs (r.val + 1) t u G₀)
      (4 * R ^ 2 / N).toNNReal (externalFieldVecLaw N μh) := by
  constructor
  · intro s
    exact (integral_exp_parisiAuxPairPressure_clipped_field_mean_le μh hN ξ ms qs r hm u ht
      G₀ hreach hR s).1
  · intro s
    have hb := (integral_exp_parisiAuxPairPressure_clipped_field_mean_le μh hN ξ ms qs r hm u ht
      G₀ hreach hR s).2
    unfold mgf
    rw [Real.coe_toNNReal _ (by positivity : 0 ≤ 4 * R ^ 2 / (N : ℝ))]
    convert hb using 1 <;> congr 1 <;> ring

/-- A positive field cutoff gives an exponential upper-tail bound
for the actual conditional pressure, uniformly in time, level and overlap. -/
theorem measure_parisiAuxPairPressure_clipped_field_mean_ge_le {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    (μh : Measure ℝ) [IsProbabilityMeasure μh]
    (hN : 0 < N) (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (hm : ParisiMAdmissible ms) {t : ℝ} (u : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 ≤ ε) :
    (externalFieldVecLaw N μh).real {a : Fin N → ℝ | ε ≤
      parisiAuxPairPressure ξ ms qs (r.val + 1) t u G₀
        (sharedReplicaSiteField (fun i => Aristotle.clip R (a i))) -
      randomFieldParisiAuxPairPressure (μh.map (Aristotle.clip R)) ξ ms qs (r.val + 1) t u G₀} ≤
      Real.exp (-(N : ℝ) * ε ^ 2 / (8 * R ^ 2)) := by
  have hb := (hasSubgaussianMGF_parisiAuxPairPressure_clipped_field_mean μh hN ξ ms qs r hm u ht
    G₀ hreach hR.le).measure_ge_le hε
  rw [Real.coe_toNNReal _ (by positivity : 0 ≤ 4 * R ^ 2 / (N : ℝ))] at hb
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : -ε ^ 2 / (2 * (4 * R ^ 2 / (N : ℝ))) =
      -(N : ℝ) * ε ^ 2 / (8 * R ^ 2) := by
    field_simp
    ring
  rw [he] at hb
  exact hb

end SpinGlass
