import SpinGlass.Parisi.Coupled.CoupledSecondDeriv

/-!
# Coupling Taylor bounds under a probability field law

The pointwise bound from Lemma 14.6.5 is averaged over the common external
field of both replicas. Integrability at other couplings follows from the
uniform first derivative bound. The concrete zero-coupling specialization
uses a finite first field moment and the actual cascade moment, giving the
coupling gain in (14.330)-(14.331).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

noncomputable section

variable {κ : ℕ} {J : Type*} [Fintype J]

private theorem integrable_family_of_unit_derivative
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F G : ℝ → Ω → ℝ} (hmeas : ∀ l, Measurable (F l))
    (hD : ∀ l h, HasDerivAt (fun x => F x h) (G l h) l)
    (hG : ∀ l h, |G l h| ≤ 1) (hY : Integrable (F 0) μ) (lam : ℝ) :
    Integrable (F lam) μ := by
  have hpoint : ∀ h, |F lam h - F 0 h| ≤ |lam| := by
    intro h
    have hh := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun l => F l h) (f' := fun l => G l h) (C := (1 : ℝ))
      (fun l _ => (hD l h).hasDerivWithinAt)
      (fun l _ => by rw [Real.norm_eq_abs]; exact hG l h) (mem_univ 0) (mem_univ lam)
    simpa only [Real.norm_eq_abs, sub_zero, one_mul] using hh
  have hdiff : Integrable (fun h => F lam h - F 0 h) μ :=
    Integrable.of_bound ((hmeas lam).sub (hmeas 0)).aestronglyMeasurable |lam|
      (.of_forall fun h => by rw [Real.norm_eq_abs]; exact hpoint h)
  exact (hdiff.add hY).congr (.of_forall fun _ => sub_add_cancel _ _)

/-- Integrability at zero coupling propagates to every coupling because
the one-site coupled recursion has slope bounded by one, uniformly in h. -/
theorem integrable_pairSiteY₀_commonField_of_integrable_at_zero
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (ns : Fin κ → ℝ) (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1)
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0)
    (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ)
    (hY : Integrable (fun h : ℝ => pairSiteY₀ ns v₀ vs 0 (fun _ => h) K₀ K) μh)
    (lam : ℝ) :
    Integrable (fun h : ℝ => pairSiteY₀ ns v₀ vs lam (fun _ => h) K₀ K) μh := by
  apply integrable_family_of_unit_derivative
    (F := fun l h => pairSiteY₀ ns v₀ vs l (fun _ => h) K₀ K)
    (G := fun l h => pairSiteY₀' ns v₀ vs l (fun _ => h) K₀ K) ?_ ?_ ?_ hY lam
  · intro l
    have hmap : Measurable (fun h : ℝ => (l, h)) := measurable_const.prodMk measurable_id
    have hjoint := measurable_pairSiteY₀_commonField ns v₀ vs K₀ K
    have hcomp := hjoint.comp hmap
    change Measurable (fun h : ℝ => pairSiteY₀ ns v₀ vs l (fun _ => h) K₀ K)
    exact hcomp
  · intro l h
    exact hasDerivAt_pairSiteY₀ ns hpos hle v₀ vs l (fun _ => h) K₀ K
  · intro l h
    exact abs_pairSiteY₀'_le_one ns hpos hle v₀ vs l (fun _ => h) K₀ K

/-- Lemma 14.6.5 after the common field average. Only integrability at zero
coupling is required, with all other domination supplied by the recursion. -/
theorem randomFieldPairSiteY₀_le_taylor
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (ns : Fin κ → ℝ) (hmono : Monotone ns) (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1)
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0)
    (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ)
    (hY : Integrable (fun h : ℝ => pairSiteY₀ ns v₀ vs 0 (fun _ => h) K₀ K) μh)
    (lam : ℝ) :
    randomFieldPairSiteY₀ μh ns v₀ vs lam K₀ K ≤ randomFieldPairSiteY₀ μh ns v₀ vs 0 K₀ K +
      randomFieldPairSiteY₀' μh ns v₀ vs 0 K₀ K * lam + lam ^ 2 / 2 := by
  have hYlam := integrable_pairSiteY₀_commonField_of_integrable_at_zero
    ns hpos hle v₀ vs K₀ K hY lam
  have hd : Integrable (fun h : ℝ => pairSiteY₀' ns v₀ vs 0 (fun _ => h) K₀ K) μh :=
    Integrable.of_bound
      (measurable_pairSiteY₀'_commonField ns hpos hle v₀ vs 0 K₀ K).aestronglyMeasurable
      1 (.of_forall fun h => by
        rw [Real.norm_eq_abs]; exact abs_pairSiteY₀'_le_one ns hpos hle v₀ vs 0 (fun _ => h) K₀ K)
  have hs : Integrable (fun h : ℝ => pairSiteY₀ ns v₀ vs 0 (fun _ => h) K₀ K +
      pairSiteY₀' ns v₀ vs 0 (fun _ => h) K₀ K * lam) μh := hY.add (hd.mul_const lam)
  have hh := integral_mono hYlam (hs.add (integrable_const (lam ^ 2 / 2)))
    (fun h => pairSiteY₀_le_taylor ns v₀ vs lam (fun _ => h) K₀ K hmono hpos hle)
  simp only [Pi.add_apply] at hh
  rw [integral_add hs (integrable_const (lam ^ 2 / 2)),
    integral_add hY (hd.mul_const lam), integral_mul_const, integral_const] at hh
  simpa only [randomFieldPairSiteY₀, randomFieldPairSiteY₀', probReal_univ, one_smul] using hh

/-- The explicit coupling λ=−(Y₀'(0)−u) gives the gain (14.330),
after averaging a common external field. -/
theorem randomFieldPairSiteY₀_sub_coupling_le_gain
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (ns : Fin κ → ℝ) (hmono : Monotone ns) (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1)
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0)
    (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ)
    (hY : Integrable (fun h : ℝ => pairSiteY₀ ns v₀ vs 0 (fun _ => h) K₀ K) μh)
    (u : ℝ) :
    let β := randomFieldPairSiteY₀' μh ns v₀ vs 0 K₀ K - u
    randomFieldPairSiteY₀ μh ns v₀ vs (-β) K₀ K + β * u ≤
      randomFieldPairSiteY₀ μh ns v₀ vs 0 K₀ K - β ^ 2 / 2 := by
  have hh := randomFieldPairSiteY₀_le_taylor ns hmono hpos hle v₀ vs K₀ K hY
    (-(randomFieldPairSiteY₀' μh ns v₀ vs 0 K₀ K - u))
  dsimp only
  nlinarith

/-- The gain (14.331) with the zero-coupling value and slope identified
by their concrete cascade expectations. A finite first field moment is
sufficient; both replicas share this field coordinate. -/
theorem randomFieldPairSiteY₀_coupling_zero_le_gain
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ms : Fin κ → ℝ) (hmono : Monotone ms) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) {τ : ℕ} (hτ : 1 ≤ τ) (u : ℝ) :
    let β := (∫ h, ∫ a, cascadeTiltTanhSq ms vs (τ - 1) (h + a) ∂gaussianReal 0 v₀ ∂μh) - u
    randomFieldPairSiteY₀ μh (halveBelow (τ - 1) ms) v₀ vs (-β)
        (couplingFactorSgn 1 τ 0) (fun p => couplingFactorSgn 1 τ (p.val + 1)) + β * u ≤
      2 * (∫ h, ∫ a, logCoshRec κ ms vs (h + a) ∂gaussianReal 0 v₀ ∂μh) - β ^ 2 / 2 := by
  have hY : Integrable (fun h : ℝ => pairSiteY₀ (J := Fin 2)
      (halveBelow (τ - 1) ms) v₀ vs 0 (fun _ => h)
      (couplingFactorSgn 1 τ 0) (fun p => couplingFactorSgn 1 τ (p.val + 1))) μh := by
    have hi := (integrable_integral_logCoshRec_externalField hμ ms vs hpos hle v₀).const_mul 2
    exact hi.congr (.of_forall fun h => (pairSiteY₀_coupling_zero ms hpos v₀ vs h hτ).symm)
  have hzero : randomFieldPairSiteY₀ μh (halveBelow (τ - 1) ms) v₀ vs 0
      (couplingFactorSgn 1 τ 0) (fun p => couplingFactorSgn 1 τ (p.val + 1)) =
      2 * (∫ h, ∫ a, logCoshRec κ ms vs (h + a) ∂gaussianReal 0 v₀ ∂μh) := by
    unfold randomFieldPairSiteY₀
    simp_rw [pairSiteY₀_coupling_zero ms hpos v₀ vs _ hτ]
    rw [integral_const_mul]
  have hderiv : randomFieldPairSiteY₀' μh (halveBelow (τ - 1) ms) v₀ vs 0
      (couplingFactorSgn 1 τ 0) (fun p => couplingFactorSgn 1 τ (p.val + 1)) =
      ∫ h, ∫ a, cascadeTiltTanhSq ms vs (τ - 1) (h + a) ∂gaussianReal 0 v₀ ∂μh := by
    unfold randomFieldPairSiteY₀'
    exact integral_congr_ae (.of_forall fun h => pairSiteY₀'_coupling_zero ms hpos hle v₀ vs h hτ)
  have hh := randomFieldPairSiteY₀_sub_coupling_le_gain (halveBelow (τ - 1) ms)
    (halveBelow_monotone hmono hpos _) (halveBelow_pos hpos _) (halveBelow_le_one hle _)
    v₀ vs (couplingFactorSgn 1 τ 0) (fun p => couplingFactorSgn 1 τ (p.val + 1)) hY u
  simpa only [hzero, hderiv] using hh

end

end SpinGlass
