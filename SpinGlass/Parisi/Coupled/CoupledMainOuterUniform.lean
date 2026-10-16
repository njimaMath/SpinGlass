import SpinGlass.Parisi.Coupled.CoupledOuterFreeContinuity
import SpinGlass.Parisi.Coupled.CoupledCompactWitness

/-!
# Uniform far outer-overlap pressure gaps

The scalar witnesses give an open cover of the compact time-overlap
region. Its finite subcover yields a gap independent of time, overlap,
finite volume and probability realization of the Hamiltonian.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- Compact uniformization of the concrete coupling-or-mass
alternative on a single far outer interval. The nonzero mass response
is the previously proved scalar conclusion used by this bridge. -/
theorem exists_randomFieldParisiAuxPairPressure_outer_far_uniform_gap_of_massResponse
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t₀ ρ : ℝ}
    (ht₀ : t₀ ∈ Ico (0 : ℝ) 1)
    (hd : ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (qs p) (qExt qs (p.val + 2)),
      ρ ≤ u - qs p → parisiLeftResponseGap μh ξ ms qs p t u = 0 →
      parisiLeftU μh ξ ms qs p (t * (deriv ξ u - deriv ξ (qs p))) -
        t * (parisiTheta ξ u - parisiTheta ξ (qs p)) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (qs p) (qExt qs (p.val + 2)),
      ρ ≤ u - qs p →
      ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
        (Pm : Measure Ω) [IsProbabilityMeasure Pm],
      ∀ G₀ : GaussianField (α := Config N) Pm
        (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
      (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
      randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 1) t u G₀ ≤
        2 * parisiInterpolationBracket μh ξ ms qs t - δ := by
  let R : Set (ℝ × ℝ) := Icc (0 : ℝ) t₀ ×ˢ Icc (qs p) (qExt qs (p.val + 2))
  let S : Set (ℝ × ℝ) := R ∩ {x | ρ ≤ x.2 - qs p}
  let B := {b : ℝ // b ∈ Ioo (mExt ms p.val) (2 * mExt ms (p.val + 1))}
  let W := Unit ⊕ B
  let g : W → ℝ × ℝ → ℝ := fun w x => match w with
    | .inl _ => parisiLeftResponseGap μh ξ ms qs p x.1 x.2 ^ 2 / 2
    | .inr b => 2 * parisiInterpolationBracket μh ξ ms qs x.1 -
        parisiOuterFreeScalarBound μh ξ ms qs p x.1 x.2 b.1
  have hcompact : IsCompact S := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const (continuous_snd.sub continuous_const))
  have hcont (w : W) : ContinuousOn (g w) S := by
    cases w with
    | inl _ =>
      exact (((continuousOn_parisiLeftResponseGap_time_overlap (μh := μh) hξ ms qs p hm hq
        ⟨ht₀.1, ht₀.2.le⟩).pow 2).div_const 2).mono inter_subset_left
    | inr b =>
      exact ((((continuous_parisiInterpolationBracket_time μh ξ ms qs).comp continuous_fst).const_mul 2).continuousOn.sub
        (continuousOn_parisiOuterFreeScalarBound_time_overlap hμ hξ ms qs p hq t₀ b.1)).mono inter_subset_left
  have hpoint (x : ℝ × ℝ) (hx : x ∈ S) : ∃ w : W, 0 < g w x := by
    have ht01 : x.1 ∈ Icc (0 : ℝ) 1 := ⟨hx.1.1.1, hx.1.1.2.trans ht₀.2.le⟩
    by_cases hz : parisiLeftResponseGap μh ξ ms qs p x.1 x.2 = 0
    · obtain ⟨b, hb, hgain⟩ := exists_parisiOuterFreeScalarBound_lt_of_deriv_ne_zero hμ hξ ms qs p hm hq
        ht01 hx.1.2 (hd x.1 hx.1.1 x.2 hx.1.2 hx.2 hz)
      exact ⟨.inr ⟨b, hb⟩, sub_pos.2 hgain⟩
    · exact ⟨.inl (), div_pos (sq_pos_of_ne_zero hz) (by norm_num)⟩
  obtain ⟨δ, hδ, hcover⟩ := exists_uniform_positive_continuous_witness hcompact g hcont hpoint
  refine ⟨δ, hδ, ?_⟩
  intro t ht u hu hdist N hN Ω _ Pm _ G₀ hreach
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.2.le⟩
  obtain ⟨w, hw⟩ := hcover (t, u) ⟨⟨ht, hu⟩, hdist⟩
  cases w with
  | inl _ =>
    have hb := randomFieldParisiAuxPairPressure_outer_le_gain hμ hN hξ ms qs p hm hq ht01 hu G₀ hreach
    change δ ≤ parisiLeftResponseGap μh ξ ms qs p t u ^ 2 / 2 at hw
    linarith
  | inr b =>
    have hb0 : 0 < b.1 := lt_of_le_of_lt (mExt_nonneg (fun i => (hm.2.1 i).le) _) b.2.1
    have hb := randomFieldParisiAuxPairPressure_outer_free_le_scalarBound hμ hN hξ ms qs p hm hq
      ht01 hu hb0 b.2.1.le b.2.2.le G₀ hreach
    change δ ≤ 2 * parisiInterpolationBracket μh ξ ms qs t -
      parisiOuterFreeScalarBound μh ξ ms qs p t u b.1 at hw
    linarith

/-- Proposition 14.8.5 on every far outer interval. The
MIN tolerance depends only on the profile, time cutoff and separation.
For each resulting MIN, one positive pressure gap works for all levels,
times, overlaps, volumes and Gaussian probability realizations. -/
theorem exists_uniform_randomFieldParisiAuxPairPressure_outer_far_gap
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {t₀ ρ : ℝ}
    (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ {μh : Measure ℝ} [IsProbabilityMeasure μh], Integrable id μh →
      ∀ {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → ParisiQAdmissible qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ p : Fin (k + 1), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (qs p) (qExt qs (p.val + 2)), ρ ≤ u - qs p →
      ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
        (Pm : Measure Ω) [IsProbabilityMeasure Pm],
      ∀ G₀ : GaussianField (α := Config N) Pm
        (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
      (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
      randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 1) t u G₀ ≤
        2 * parisiInterpolationBracket μh ξ ms qs t - δ := by
  classical
  obtain ⟨ε, hε, η, hη, hd⟩ := exists_uniform_outer_massResponse_neg_of_coupling_eq_zero hξ ht₀ hρ
  refine ⟨ε, hε, ?_⟩
  intro μh _ hμ k ms qs hm hq hfull hnear
  have hex (p : Fin (k + 1)) :=
    exists_randomFieldParisiAuxPairPressure_outer_far_uniform_gap_of_massResponse hμ hξ ms qs p hm hq ht₀
      (fun t ht u hu hdist hzero =>
        ne_of_lt ((hd hμ ms qs hm hq hfull hnear p t ht u hu hdist hzero).trans_lt (by linarith [hη])))
  choose d hdp hlevel using hex
  obtain ⟨δ, hδ, hδp⟩ := exists_uniform_positive_lower_bound_of_finite d hdp
  refine ⟨δ, hδ, ?_⟩
  intro p t ht u hu hdist N hN Ω _ Pm _ G₀ hreach
  exact (hlevel p t ht u hu hdist N hN Ω Pm G₀ hreach).trans
    (sub_le_sub_left (hδp p) _)

end SpinGlass
