import SpinGlass.Parisi.Coupled.CoupledMainFar

/-!
# Continuous witnesses away from the stationary overlap

The local response signs cover small displacements; the far trial
cover treats all others. The MIN tolerance precedes the parameters,
so a parameter-dependent compact exclusion radius can be chosen later.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The far-region trial cover for Theorem 14.5.7. All witnesses are
concrete and selected before finite volume or a Gaussian realization. -/
theorem exists_uniform_parisiMainTrial_positive_offCenter_gap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ r : Fin (k + 1), ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 1,
      u ≠ qs r → ∃ w : ParisiMainTrial ms qs r,
        0 < parisiMainTrialGap μh ξ ms qs r w t u := by
  obtain ⟨εI, hεI, ρ, hρ, hcritical⟩ := exists_uniform_parisi_critical_response_gap hξ hμ ht₀
  obtain ⟨εO, hεO, hfar⟩ := exists_uniform_parisiMainTrial_positive_far_gap hμ hξ ht₀ hρ
  obtain ⟨εP, hεP, hroot⟩ := exists_uniform_parisi_root_nonnegative_response_gap hξ hμ ht₀
  obtain ⟨εS, hεS, hsigned⟩ := exists_uniform_parisi_root_signed_response_gap hξ hμ ht₀
  let ε := min (min εI εO) (min εP εS)
  have hε : 0 < ε := lt_min (lt_min hεI hεO) (lt_min hεP hεS)
  refine ⟨ε, hε, ?_⟩
  intro k ms qs hm hmin hfull hnear r t ht u hu hne
  have hnearI := hnear.trans_le (add_le_add le_rfl ((min_le_left _ _).trans (min_le_left εI εO)))
  have hnearO := hnear.trans_le (add_le_add le_rfl ((min_le_left _ _).trans (min_le_right εI εO)))
  have hnearP := hnear.trans_le (add_le_add le_rfl ((min_le_right _ _).trans (min_le_left εP εS)))
  have hnearS := hnear.trans_le (add_le_add le_rfl ((min_le_right _ _).trans (min_le_right εP εS)))
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.2.le⟩
  by_cases hdist : ρ ≤ |u - qs r|
  · exact hfar k ms qs hm hmin hfull hnearO r t ht u hu hdist
  have hsmall : |u - qs r| ≤ ρ := (lt_of_not_ge hdist).le
  have hc := hcritical k ms qs hm hmin hfull hnearI t ht
  by_cases hexception : r.val = 0 ∧ |u| ≤ qs 0
  · have hr : r = 0 := Fin.ext hexception.1
    subst r
    have huq : u < qs 0 := lt_of_le_of_ne ((le_abs_self u).trans hexception.2) hne
    have hsep : 0 < (1 - t₀) / 2 * (qs 0 - u) :=
      mul_pos (div_pos (sub_pos.2 ht₀.2) (by norm_num)) (sub_pos.2 huq)
    exact exists_parisiMainTrial_positive_root_gap_of_response hμ.integrable_id hξ ms qs hm
      hmin.1 ht01 hexception.2
      (fun huP => (hsep.trans_le (hroot k ms qs hm hmin hfull hnearP t ht u huP)).ne')
      (fun huS => (hsep.trans_le (hsigned k ms qs hm hmin hfull hnearS t ht u huS)).ne')
  · by_cases hinside : u ∈ Icc (qExt qs r.val) (qExt qs (r.val + 2))
    · rcases le_total u (qs r) with hleft | hright
      · cases r using Fin.cases with
        | zero =>
          have hu0 : 0 ≤ u := by simpa only [Fin.val_zero, qExt_zero] using hinside.1
          exact (hexception ⟨rfl, by rwa [abs_of_nonneg hu0]⟩).elim
        | succ p =>
          have huI : u ∈ Icc (qs p.castSucc) (qs p.succ) := by
            constructor
            · have hL := hinside.1
              rw [Fin.val_succ, qExt_succ_of_lt qs (by omega : p.val < k + 1)] at hL
              exact hL
            · exact hleft
          have hdistI : qs p.succ - u ≤ ρ := by
            rw [abs_of_nonpos (sub_nonpos.2 hleft)] at hsmall
            linarith
          have hresponse : parisiRightResponseGap μh ξ ms qs p t u ≠ 0 := by
            have hh := hc.2.1 p u huI hdistI
            have hp : 0 < (1 - t₀) / 4 * (qs p.succ - u) :=
              mul_pos (div_pos (sub_pos.2 ht₀.2) (by norm_num))
                (sub_pos.2 (lt_of_le_of_ne hleft hne))
            exact (hp.trans_le hh).ne'
          obtain ⟨w, hw⟩ := exists_parisiInnerFreeTrial_positive_gap_of_massResponse
            hμ.integrable_id hξ ms qs p hm hmin.1 ht01 huI (fun hz => (hresponse hz).elim)
          exact ⟨.inner p rfl w, hw⟩
      · have huO : u ∈ Icc (qs r) (qExt qs (r.val + 2)) := ⟨hright, hinside.2⟩
        have hdistO : u - qs r ≤ ρ := by rwa [abs_of_nonneg (sub_nonneg.2 hright)] at hsmall
        have hresponse : parisiLeftResponseGap μh ξ ms qs r t u ≠ 0 := by
          have hh := hc.2.2 r u huO hdistO
          have hp : 0 < (1 - t₀) / 4 * (u - qs r) :=
            mul_pos (div_pos (sub_pos.2 ht₀.2) (by norm_num))
              (sub_pos.2 (lt_of_le_of_ne hright hne.symm))
          intro hz
          rw [hz] at hh
          linarith
        obtain ⟨w, hw⟩ := exists_parisiOuterFreeTrial_positive_gap_of_massResponse
          hμ.integrable_id hξ ms qs r hm hmin.1 ht01 huO (fun hz => (hresponse hz).elim)
        exact ⟨.outer w, hw⟩
    · have houtside : u < qExt qs r.val ∨ qExt qs (r.val + 2) < u := by
        by_cases hleft : u < qExt qs r.val
        · exact Or.inl hleft
        · exact Or.inr (lt_of_not_ge (fun hright => hinside ⟨le_of_not_gt hleft, hright⟩))
      obtain ⟨w, hw⟩ := exists_parisiCanonicalTrial_positive_outside_gap hμ hξ ms qs hm hmin r
        ht₀ ht hu houtside hexception
      exact ⟨.canonical w, hw⟩

/-- Any compact exclusion of the stationary overlaps has one physical
pressure gap uniform over levels, time, overlap, volume and Gaussian law.
The trial-cover hypothesis is the preceding concrete book-level conclusion. -/
theorem exists_uniform_randomFieldParisiAuxPairPressure_offCenter_gap_of_trialCover
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t₀ ρ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) (hρ : 0 < ρ)
    (htrial : ∀ r : Fin (k + 1), ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 1,
      u ≠ qs r → ∃ w : ParisiMainTrial ms qs r,
        0 < parisiMainTrialGap μh ξ ms qs r w t u) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : Fin (k + 1), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (-1 : ℝ) 1, ρ ≤ |u - qs r| →
      ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
        (Pm : Measure Ω) [IsProbabilityMeasure Pm],
      ∀ G₀ : GaussianField (α := Config N) Pm
        (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
      (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
      randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t u G₀ ≤
        2 * parisiInterpolationBracket μh ξ ms qs t - δ := by
  classical
  let S (r : Fin (k + 1)) : Set (ℝ × ℝ) :=
    (Icc (0 : ℝ) t₀ ×ˢ Icc (-1 : ℝ) 1) ∩ {x | ρ ≤ |x.2 - qs r|}
  have hcompact (r : Fin (k + 1)) : IsCompact (S r) :=
    (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_snd.sub continuous_const).abs)
  have hex (r : Fin (k + 1)) : ∃ δ : ℝ, 0 < δ ∧
      ∀ t u : ℝ, (t, u) ∈ S r →
      ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
        (Pm : Measure Ω) [IsProbabilityMeasure Pm],
      ∀ G₀ : GaussianField (α := Config N) Pm
        (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
      (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
      randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t u G₀ ≤
        2 * parisiInterpolationBracket μh ξ ms qs t - δ := by
    let g := fun w : ParisiMainTrial ms qs r => fun x : ℝ × ℝ =>
      parisiMainTrialGap μh ξ ms qs r w x.1 x.2
    have hc (w) : ContinuousOn (g w) (S r) :=
      (continuous_parisiMainTrialGap_time_overlap hμ hξ ms qs hm hq r w).continuousOn
    have hp (x : ℝ × ℝ) (hx : x ∈ S r) : ∃ w, 0 < g w x := by
      apply htrial r x.1 hx.1.1 x.2 hx.1.2
      intro he
      have hd := hx.2
      change ρ ≤ |x.2 - qs r| at hd
      rw [he, sub_self, abs_zero] at hd
      linarith
    obtain ⟨δ, hδ, hcover⟩ := exists_uniform_positive_continuous_witness (hcompact r) g hc hp
    refine ⟨δ, hδ, ?_⟩
    intro t u htu N hN Ω _ Pm _ G₀ hreach
    obtain ⟨w, hw⟩ := hcover (t, u) htu
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨htu.1.1.1, htu.1.1.2.trans ht₀.2.le⟩
    have hb := randomFieldParisiAuxPairPressure_le_mainTrialGap hμ hN hξ ms qs hm hq r w u ht01 G₀ hreach
    dsimp only [g] at hw
    linarith
  choose d hd hbound using hex
  obtain ⟨δ, hδ, hδr⟩ := exists_uniform_positive_lower_bound_of_finite d hd
  refine ⟨δ, hδ, ?_⟩
  intro r t ht u hu hdist N hN Ω _ Pm _ G₀ hreach
  exact (hbound r t u ⟨⟨ht, hu⟩, hdist⟩ N hN Ω Pm G₀ hreach).trans
    (sub_le_sub_left (hδr r) _)

end SpinGlass
