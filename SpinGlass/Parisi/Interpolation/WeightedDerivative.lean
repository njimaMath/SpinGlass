import SpinGlass.Parisi.Guerra.GuerraBound

/-!
# Exact weighted Gaussian interpolation

The finite weighted pressure has the full Guerra derivative. Restriction
to the support handles zero weights without differentiating their logarithms.
These identities are the finite-tree input for the lower interpolation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace SpinGlass.FiniteGibbs

noncomputable section

variable {α Ω : Type*} [Fintype α] [MeasurableSpace Ω] {P : Measure Ω}
    {K₁ K₂ : α → α → ℝ}
    (G₁ : GaussianField (α := α) P K₁) (G₂ : GaussianField (α := α) P K₂)

/-- The expected weighted pressure along the actual Gaussian pair law. -/
def wGuerraPhi (wt : α → ℝ) (c : EnergySpace α) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ p : PairSpace α, wFreeEnergy wt n (gaussianInterp t p + c) ∂pairLaw G₁ G₂

theorem wGuerraPhi_eq_integral
    (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (c : EnergySpace α) (n : ℕ) (t : ℝ) :
    wGuerraPhi G₁ G₂ wt c n t =
      ∫ ω, wFreeEnergy wt n (gaussianInterp t (pair G₁ G₂ ω) + c) ∂P := by
  have hc : Continuous (wFreeEnergy wt n) :=
    continuous_const.mul ((continuous_wZ wt).log (fun H => (wZ_pos wt hwt hne H).ne'))
  have hm : AEStronglyMeasurable
      (fun p : PairSpace α => wFreeEnergy wt n (gaussianInterp t p + c)) (pairLaw G₁ G₂) :=
    (hc.comp ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable
  exact integral_map (measurable_pair G₁ G₂).aemeasurable hm

theorem integral_wGuerraTrace_eq_integral
    (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (c : EnergySpace α) (n : ℕ) (t : ℝ) :
    (∫ p : PairSpace α, wGuerraTrace wt K₁ K₂ n (gaussianInterp t p + c) ∂pairLaw G₁ G₂) =
      ∫ ω, wGuerraTrace wt K₁ K₂ n (gaussianInterp t (pair G₁ G₂ ω) + c) ∂P := by
  have hm : AEStronglyMeasurable
      (fun p : PairSpace α => wGuerraTrace wt K₁ K₂ n (gaussianInterp t p + c))
      (pairLaw G₁ G₂) :=
    ((continuous_wGuerraTrace wt hwt hne K₁ K₂ n).comp
      ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable
  exact integral_map (measurable_pair G₁ G₂).aemeasurable hm

theorem wGuerraPhi_eq_guerraPhi_support (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    [Nonempty (Support wt)] (c : EnergySpace α) (n : ℕ) (t : ℝ) :
    wGuerraPhi G₁ G₂ wt c n t =
      guerraPhi (G₁.comp (Subtype.val : Support wt → α)) (G₂.comp Subtype.val)
        (shiftHam wt c) n t := by
  unfold guerraPhi
  have hm : AEStronglyMeasurable (fun p : PairSpace (Support wt) =>
      free_energy_density n (gaussianInterp t p + shiftHam wt c))
      ((pairLaw G₁ G₂).map (pairPullback wt)) :=
    ((contDiff_free_energy_density n).continuous.comp
      ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable
  rw [pairLaw_comp, integral_map (measurable_pairPullback wt).aemeasurable
    hm]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  change wFreeEnergy wt n (gaussianInterp t p + c) =
    free_energy_density n (gaussianInterp t (pairPullback wt p) + shiftHam wt c)
  rw [wFreeEnergy_eq wt hwt, gaussianInterp_pairPullback, shiftHam_add]

theorem integral_wGuerraTrace_eq_support (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    [Nonempty (Support wt)] (c : EnergySpace α) (n : ℕ) (t : ℝ) :
    (∫ p : PairSpace α, wGuerraTrace wt K₁ K₂ n (gaussianInterp t p + c)
      ∂pairLaw G₁ G₂) =
    ∫ p : PairSpace (Support wt), guerraTrace
      (fun x y => K₁ x.val y.val) (fun x y => K₂ x.val y.val) n
      (gaussianInterp t p + shiftHam wt c)
      ∂pairLaw (G₁.comp (Subtype.val : Support wt → α)) (G₂.comp Subtype.val) := by
  have hm : AEStronglyMeasurable (fun p : PairSpace (Support wt) =>
      guerraTrace (fun x y => K₁ x.val y.val) (fun x y => K₂ x.val y.val) n
        (gaussianInterp t p + shiftHam wt c))
      ((pairLaw G₁ G₂).map (pairPullback wt)) :=
    ((continuous_guerraTrace _ _ n).comp
      ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable
  rw [pairLaw_comp, integral_map (measurable_pairPullback wt).aemeasurable
    hm]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  change wGuerraTrace wt K₁ K₂ n (gaussianInterp t p + c) =
    guerraTrace (fun x y => K₁ x.val y.val) (fun x y => K₂ x.val y.val) n
      (gaussianInterp t (pairPullback wt p) + shiftHam wt c)
  rw [wGuerraTrace_eq wt hwt, gaussianInterp_pairPullback, shiftHam_add]

/-- Exact finite-tree Gaussian integration by parts, before any covariance
comparison or remainder estimate. -/
theorem hasDerivAt_wGuerraPhi (hindep : G₁.U ⟂ᵢ[P] G₂.U)
    (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (c : EnergySpace α) (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (wGuerraPhi G₁ G₂ wt c n)
      (∫ p : PairSpace α, wGuerraTrace wt K₁ K₂ n (gaussianInterp t p + c)
        ∂pairLaw G₁ G₂) t := by
  let : Nonempty (Support wt) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  rw [show wGuerraPhi G₁ G₂ wt c n =
      guerraPhi (G₁.comp (Subtype.val : Support wt → α)) (G₂.comp Subtype.val)
        (shiftHam wt c) n from funext (wGuerraPhi_eq_guerraPhi_support G₁ G₂ wt hwt c n),
    integral_wGuerraTrace_eq_support G₁ G₂ wt hwt c n]
  exact hasDerivAt_guerraPhi _ _
    (GaussianField.comp_indepFun hindep (Subtype.val : Support wt → α) Subtype.val) _ _ ht

theorem continuousOn_wGuerraPhi (hindep : G₁.U ⟂ᵢ[P] G₂.U)
    (wt : α → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (c : EnergySpace α) (n : ℕ) :
    ContinuousOn (wGuerraPhi G₁ G₂ wt c n) (Icc (0 : ℝ) 1) := by
  let : Nonempty (Support wt) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  rw [show wGuerraPhi G₁ G₂ wt c n =
      guerraPhi (G₁.comp (Subtype.val : Support wt → α)) (G₂.comp Subtype.val)
        (shiftHam wt c) n from funext (wGuerraPhi_eq_guerraPhi_support G₁ G₂ wt hwt c n)]
  exact continuousOn_guerraPhi _ _
    (GaussianField.comp_indepFun hindep (Subtype.val : Support wt → α) Subtype.val) _ _

end

end SpinGlass.FiniteGibbs
