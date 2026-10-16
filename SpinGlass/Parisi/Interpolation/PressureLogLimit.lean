import SpinGlass.Parisi.Interpolation.PressureBranchMoments

/-!
# The Gaussian mean limit of the logarithmic cascade partition

A fixed configuration on a positive branch gives an integrable lower
bound. The existing monotone partition approximation then passes its
logarithm through the full disorder/root/marks expectation.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

theorem integrable_branchHamX_gaussianLaw
    (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (t : ℝ) (h : Fin N → ℝ)
    (α : Fin k → ℕ × ℕ) (σ : Config N) :
    Integrable (fun q : (EnergySpace N × (Fin N → ℝ)) × CascadeMarks (Fin N → ℝ) k =>
      branchHamX N k t h q.1.1 q.1.2 (branchMarks k q.2 α) σ)
      (((gaussField N (overlapCovMatrix N ξ)).prod
        (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀))).prod
          (cascadeMarksLaw k (gaussianMarks N k vs))) := by
  let Pm := gaussField N (overlapCovMatrix N ξ)
  let Pz := Measure.pi (fun _ : Fin N => gaussianReal 0 v₀)
  let Pc := cascadeMarksLaw k (gaussianMarks N k vs)
  have hH : Integrable (fun H : EnergySpace N => H σ) Pm := by
    apply (GaussianField.ofMultivariateGaussian hS).integrable.norm.mono'
      (by fun_prop)
    exact Filter.Eventually.of_forall fun H => PiLp.norm_apply_le H σ
  have hr (i : Fin N) : Integrable (fun z : Fin N → ℝ => z i) Pz :=
    ((measurePreserving_eval (μ := fun _ : Fin N => gaussianReal 0 v₀) i).integrable_comp
      measurable_id.aestronglyMeasurable).2 (integrable_id_gaussianReal 0 v₀)
  have hb (p : Fin k) (i : Fin N) :
      Integrable (fun z : CascadeMarks (Fin N → ℝ) k => branchMarks k z α p i) Pc := by
    have h₁ : Integrable (fun x : Fin N → ℝ => x i) (gaussianMarks N k vs p) :=
      ((measurePreserving_eval (μ := fun _ : Fin N => gaussianReal 0 (vs p)) i).integrable_comp
        measurable_id.aestronglyMeasurable).2 (integrable_id_gaussianReal 0 (vs p))
    have h₂ : Integrable (fun x : Fin k → Fin N → ℝ => x p i)
        (Measure.pi (gaussianMarks N k vs)) :=
      ((measurePreserving_eval (μ := gaussianMarks N k vs) p).integrable_comp
        (measurable_pi_apply i).aestronglyMeasurable).2 h₁
    have hmap : MeasurePreserving (fun z => branchMarks k z α) Pc
        (Measure.pi (gaussianMarks N k vs)) :=
      ⟨measurable_branchMarks k α, cascadeMarksLaw_map_branchMarks k _ α⟩
    have hg : Measurable (fun x : Fin k → Fin N → ℝ => x p i) :=
      (measurable_pi_apply i).comp (measurable_pi_apply p)
    exact (hmap.integrable_comp hg.aestronglyMeasurable).2 h₂
  unfold branchHamX
  exact (((hH.comp_fst Pz).comp_fst Pc).const_mul _).add
    ((integrable_finsetSum _ fun i _ =>
      (((hr i).comp_snd Pm).comp_fst Pc).add
        (integrable_finsetSum _ fun p _ => (hb p i).comp_snd (Pm.prod Pz)) |>.const_mul _)
      |>.const_mul _) |>.add (integrable_const _)

theorem neg_branchHamX_le_log_hamG
    (t : ℝ) (h : Fin N → ℝ) (H : EnergySpace N) (z : Fin N → ℝ)
    (x : Fin k → Fin N → ℝ) (σ : Config N) :
    -branchHamX N k t h H z x σ ≤ Real.log (hamG N k t h H z x).toReal := by
  rw [hamG, ENNReal.toReal_ofReal (branchZX_pos N k t h H z x).le]
  have he : Real.exp (-branchHamX N k t h H z x σ) ≤ branchZX N k t h H z x :=
    Finset.single_le_sum (f := fun τ => Real.exp (-branchHamX N k t h H z x τ))
      (fun τ _ => (Real.exp_pos _).le) (Finset.mem_univ σ)
  exact (Real.log_exp _).symm.le.trans (Real.log_le_log (Real.exp_pos _) he)

theorem integrable_log_cascadeSum_hamG
    (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (t : ℝ) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞) :
    Integrable (fun q : (EnergySpace N × (Fin N → ℝ)) × CascadeMarks (Fin N → ℝ) k =>
      Real.log (cascadeSum k (hamG N k t h q.1.1 q.1.2) (cascadeZip k (w, q.2))).toReal)
      (((gaussField N (overlapCovMatrix N ξ)).prod
        (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀))).prod
          (cascadeMarksLaw k (gaussianMarks N k vs))) := by
  obtain ⟨α, hα, _, _⟩ := exists_mem_truncFinset k w hW0
  apply integrable_log_cascadeSum_of k
    ((gaussField N (overlapCovMatrix N ξ)).prod
      (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀))) (gaussianMarks N k vs)
    (fun q => hamG N k t h q.1 q.2) (measurable_hamG_fixedTime N k t h)
    (fun q x => hamG_pos N k t h q.1 q.2 x) (fun _ _ => ENNReal.ofReal_ne_top) w hW
    (lintegral_cascadeSum_hamG_ne_top N k ξ hS v₀ vs t h w hW) hα
    (integrable_branchHamX_gaussianLaw N k ξ hS v₀ vs t h α (fun _ => true)).neg
  intro q
  exact neg_branchHamX_le_log_hamG N k t h q.1.1 q.1.2 (branchMarks k q.2 α) _

/-- At fixed weights of positive finite mass, the actual logarithmic
partition converges in mean over all Gaussian disorder and marks. -/
theorem tendsto_integral_log_truncSum_hamG
    (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (t : ℝ) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞) :
    Tendsto (fun M => ∫ q, Real.log (truncSum k M w (hamG N k t h q.1.1 q.1.2) q.2).toReal
      ∂((gaussField N (overlapCovMatrix N ξ)).prod
        (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀))).prod
          (cascadeMarksLaw k (gaussianMarks N k vs))) atTop
      (𝓝 (∫ q, Real.log (cascadeSum k (hamG N k t h q.1.1 q.1.2)
        (cascadeZip k (w, q.2))).toReal
        ∂((gaussField N (overlapCovMatrix N ξ)).prod
          (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀))).prod
            (cascadeMarksLaw k (gaussianMarks N k vs)))) := by
  obtain ⟨α, hα, _, _⟩ := exists_mem_truncFinset k w hW0
  apply tendsto_integral_log_truncSum k
    ((gaussField N (overlapCovMatrix N ξ)).prod
      (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀))) (gaussianMarks N k vs)
    (fun q => hamG N k t h q.1 q.2) (measurable_hamG_fixedTime N k t h)
    (fun q x => hamG_pos N k t h q.1 q.2 x) (fun _ _ => ENNReal.ofReal_ne_top) w hW0 hW
    (lintegral_cascadeSum_hamG_ne_top N k ξ hS v₀ vs t h w hW) hα
    (integrable_branchHamX_gaussianLaw N k ξ hS v₀ vs t h α (fun _ => true)).neg
  intro q
  exact neg_branchHamX_le_log_hamG N k t h q.1.1 q.1.2 (branchMarks k q.2 α) _

end

end SpinGlass
