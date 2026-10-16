import SpinGlass.Parisi.Interpolation.TreeRemainder

/-!
# The actual truncated-tree interpolation derivative

The finite weighted Gaussian identity is instantiated with the model
disorder and the original Parisi tree marks. The derivative retains the
profile remainder, under the preserved Talagrand profile assumptions.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k M : ℕ)

def parisiTruncatedPressure (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ)
    (h : Fin N → ℝ) (w : CascadeWeights k) (t : ℝ) : ℝ :=
  (∫ ω, wFreeEnergy (branchWt (N := N) (truncWt k M w)) N (truncHam N k M t h ω)
    ∂(gaussField N (overlapCovMatrix N ξ)).prod
      (marksLaw N k (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1)))) -
    (1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α)

def parisiTruncatedGuerraRemainder (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ)
    (h : Fin N → ℝ) (w : CascadeWeights k) (t : ℝ) : ℝ :=
  ∫ ω, weightedTreeProfileRemainder ξ (treeOverlap qs)
    (branchWt (N := N) (truncWt k M w)) (truncHam N k M t h ω)
    ∂(gaussField N (overlapCovMatrix N ξ)).prod
      (marksLaw N k (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1)))

theorem continuousOn_parisiTruncatedPressure
    (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ) (w : CascadeWeights k)
    (hne : ∃ α : TruncBranch k M, truncWt k M w α ≠ 0) :
    ContinuousOn (parisiTruncatedPressure N k M ξ qs h w) (Icc (0 : ℝ) 1) := by
  let Pm := gaussField N (overlapCovMatrix N ξ)
  let Pz := marksLaw N k (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1))
  let wt := branchWt (N := N) (truncWt k M w)
  let c := pullbackCLM (Prod.fst : Config N × TruncBranch k M → Config N)
    (siteExternalFieldEnergy N h)
  let G₁ := ((GaussianField.ofMultivariateGaussian hS).comp
    (Prod.fst : Config N × TruncBranch k M → Config N)).prodLeft Pz
  let G₂ := (treeField N k M (parisiVar ξ qs 0)
    (fun p => parisiVar ξ qs (p.val + 1))).prodRight Pm
  have hindep : G₁.U ⟂ᵢ[Pm.prod Pz] G₂.U := GaussianField.prodLeft_indepFun_prodRight _ _
  have hwt (x) : 0 ≤ wt x := truncWt_nonneg k M w x.2
  have hne' : ∃ x, wt x ≠ 0 := ⟨(fun _ => true, hne.choose), hne.choose_spec⟩
  have hpath (s : ℝ) (ω : EnergySpace N × MarksSpace N k) :
      gaussianInterp s (pair G₁ G₂ ω) + c = truncHam N k M s h ω := by
    rw [gaussianInterp_apply]
    rfl
  have he : parisiTruncatedPressure N k M ξ qs h w = fun s =>
      wGuerraPhi G₁ G₂ wt c N s - (1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α) := by
    funext s
    rw [wGuerraPhi_eq_integral G₁ G₂ wt hwt hne' c N s]
    simp_rw [hpath]
    rfl
  rw [he]
  exact (continuousOn_wGuerraPhi G₁ G₂ hindep wt hwt hne' c N).sub continuousOn_const

theorem continuous_parisiTruncatedGuerraRemainder
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    (h : Fin N → ℝ) (w : CascadeWeights k)
    (hne : ∃ α : TruncBranch k M, truncWt k M w α ≠ 0) :
    Continuous (parisiTruncatedGuerraRemainder N k M ξ qs h w) := by
  let wt := branchWt (N := N) (truncWt k M w)
  have hwt (x) : 0 ≤ wt x := truncWt_nonneg k M w x.2
  have hne' : ∃ x, wt x ≠ 0 := ⟨(fun _ => true, hne.choose), hne.choose_spec⟩
  have hqt (α γ : TruncBranch k M) : treeOverlap qs α γ ∈ Icc (0 : ℝ) 1 :=
    qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _
  have hc := continuous_weightedTreeProfileRemainder ξ (treeOverlap qs) wt hwt hne'
  unfold parisiTruncatedGuerraRemainder
  apply continuous_of_dominated (bound := fun _ => deriv (deriv ξ) 1)
  · intro t
    exact (hc.measurable.comp (measurable_truncHam N k M t h)).aestronglyMeasurable
  · intro t
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg
      (weightedTreeProfileRemainder_nonneg hξ _ hqt wt hwt hne' _)]
    exact weightedTreeProfileRemainder_le_curvature hξ _ hqt wt hwt hne' _
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro ω
    apply hc.comp
    unfold truncHam
    exact ((Real.continuous_sqrt.smul continuous_const).add
      ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).smul
        continuous_const)).add continuous_const

/-- The actual finite-tree form of (14.108), with no derivative or
covariance-identification hypothesis left to the caller. -/
theorem hasDerivAt_parisiTruncatedPressure
    (hN : 0 < N) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    (h : Fin N → ℝ) (w : CascadeWeights k)
    (hne : ∃ α : TruncBranch k M, truncWt k M w α ≠ 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (parisiTruncatedPressure N k M ξ qs h w)
      (guerraTruncBound N k M ξ qs h w t - parisiTruncatedGuerraRemainder N k M ξ qs h w t) t := by
  let Pm := gaussField N (overlapCovMatrix N ξ)
  let Pz := marksLaw N k (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1))
  let wt := branchWt (N := N) (truncWt k M w)
  let c := pullbackCLM (Prod.fst : Config N × TruncBranch k M → Config N)
    (siteExternalFieldEnergy N h)
  let G₁ := ((GaussianField.ofMultivariateGaussian hS).comp
    (Prod.fst : Config N × TruncBranch k M → Config N)).prodLeft Pz
  let G₂ := (treeField N k M (parisiVar ξ qs 0)
    (fun p => parisiVar ξ qs (p.val + 1))).prodRight Pm
  have hindep : G₁.U ⟂ᵢ[Pm.prod Pz] G₂.U := GaussianField.prodLeft_indepFun_prodRight _ _
  have hwt (x) : 0 ≤ wt x := truncWt_nonneg k M w x.2
  have hne' : ∃ x, wt x ≠ 0 := ⟨(fun _ => true, hne.choose), hne.choose_spec⟩
  have hpath (s : ℝ) (ω : EnergySpace N × MarksSpace N k) :
      gaussianInterp s (pair G₁ G₂ ω) + c = truncHam N k M s h ω := by
    rw [gaussianInterp_apply]
    rfl
  have hpressure : parisiTruncatedPressure N k M ξ qs h w =
      fun s => wGuerraPhi G₁ G₂ wt c N s -
        (1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α) := by
    funext s
    rw [wGuerraPhi_eq_integral G₁ G₂ wt hwt hne' c N s]
    simp_rw [hpath]
    rfl
  have hd := (hasDerivAt_wGuerraPhi G₁ G₂ hindep wt hwt hne' c N ht).sub_const
    ((1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α))
  rw [← hpressure, integral_wGuerraTrace_eq_integral G₁ G₂ wt hwt hne' c N t] at hd
  simp_rw [hpath] at hd
  have hK := treeFieldKernel_parisi_eq_treeKernel (M := M) hN hξ qs hq
  change HasDerivAt (parisiTruncatedPressure N k M ξ qs h w)
    (∫ ω, wGuerraTrace wt (modelKernel N ξ)
      (treeFieldKernel N k M (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1))) N
      (truncHam N k M t h ω) ∂Pm.prod Pz) t at hd
  rw [hK] at hd
  simp_rw [wGuerraTrace_tree_eq_sub_remainder hN ξ (treeOverlap qs)
    (qs (Fin.last k)) (treeOverlap_self qs) wt hwt hne'] at hd
  have hqt (α γ : TruncBranch k M) : treeOverlap qs α γ ∈ Icc (0 : ℝ) 1 :=
    qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _
  have hiB : Integrable (fun ω => treeBoundIntegrand wt (ξ 1 - deriv ξ (qs (Fin.last k)))
      (fun x y => parisiTheta ξ (treeOverlap qs x.2 y.2)) (truncHam N k M t h ω)) (Pm.prod Pz) := by
    apply Integrable.of_bound
      ((continuous_treeBoundIntegrand wt hwt hne' _ _).measurable.comp
        (measurable_truncHam N k M t h)).aestronglyMeasurable
      ((1 / 2) * |ξ 1 - deriv ξ (qs (Fin.last k))| + (1 / 2) *
        ∑ x : Config N × TruncBranch k M, ∑ y : Config N × TruncBranch k M,
          |parisiTheta ξ (treeOverlap qs x.2 y.2)|)
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs]
    exact abs_treeBoundIntegrand_le wt hwt hne' _ _ _
  have hiR : Integrable (fun ω => weightedTreeProfileRemainder ξ (treeOverlap qs) wt
      (truncHam N k M t h ω)) (Pm.prod Pz) := by
    apply Integrable.of_bound
      ((continuous_weightedTreeProfileRemainder ξ _ wt hwt hne').measurable.comp
        (measurable_truncHam N k M t h)).aestronglyMeasurable (deriv (deriv ξ) 1)
    apply Filter.Eventually.of_forall
    intro ω
    dsimp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (weightedTreeProfileRemainder_nonneg hξ _ hqt wt hwt hne' _)]
    exact weightedTreeProfileRemainder_le_curvature hξ _ hqt wt hwt hne' _
  rw [integral_sub hiB hiR] at hd
  exact hd

/-- The exact integrated formula for the normalized actual finite tree,
including both closed endpoints and any shorter interpolation interval. -/
theorem parisiTruncatedPressure_sub_eq_integral
    (hN : 0 < N) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    (h : Fin N → ℝ) (w : CascadeWeights k)
    (hne : ∃ α : TruncBranch k M, truncWt k M w α ≠ 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    parisiTruncatedPressure N k M ξ qs h w b - parisiTruncatedPressure N k M ξ qs h w a =
      ∫ t in a..b, guerraTruncBound N k M ξ qs h w t -
        parisiTruncatedGuerraRemainder N k M ξ qs h w t := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · exact (continuousOn_parisiTruncatedPressure N k M ξ hS qs h w hne).mono
      (fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩)
  · intro t ht
    exact hasDerivAt_parisiTruncatedPressure N k M hN hξ hS qs hq h w hne
      ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩
  · exact ((continuous_guerraTruncBound N k M ξ qs h w hne).sub
      (continuous_parisiTruncatedGuerraRemainder N k M hξ qs hq h w hne)).intervalIntegrable a b

end

end SpinGlass
