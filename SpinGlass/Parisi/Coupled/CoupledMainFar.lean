import SpinGlass.Parisi.Coupled.CoupledMainTrial

/-!
# One continuous trial witness at every far overlap

The MIN tolerance is selected before all parameters. The actual root,
inner, outer and canonical families then cover every separated overlap,
including the neighboring boundaries and the initial root exception.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The far-region trial cover for Theorem 14.5.7. All witnesses are
concrete and selected before finite volume or a Gaussian realization. -/
theorem exists_uniform_parisiMainTrial_positive_far_gap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {t₀ ρ : ℝ}
    (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ r : Fin (k + 1), ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 1,
      ρ ≤ |u - qs r| → ∃ w : ParisiMainTrial ms qs r,
        0 < parisiMainTrialGap μh ξ ms qs r w t u := by
  obtain ⟨εI, hεI, hinner⟩ := exists_uniform_parisiInnerFreeTrial_positive_far_gap hξ ht₀ hρ
  obtain ⟨εO, hεO, houter⟩ := exists_uniform_parisiOuterFreeTrial_positive_far_gap hξ ht₀ hρ
  obtain ⟨εP, hεP, hroot⟩ := exists_uniform_parisi_root_nonnegative_response_gap hξ hμ ht₀
  obtain ⟨εS, hεS, hsigned⟩ := exists_uniform_parisi_root_signed_response_gap hξ hμ ht₀
  let ε := min (min εI εO) (min εP εS)
  have hε : 0 < ε := lt_min (lt_min hεI hεO) (lt_min hεP hεS)
  refine ⟨ε, hε, ?_⟩
  intro k ms qs hm hmin hfull hnear r t ht u hu hdist
  have hnearI := hnear.trans_le (add_le_add le_rfl ((min_le_left _ _).trans (min_le_left εI εO)))
  have hnearO := hnear.trans_le (add_le_add le_rfl ((min_le_left _ _).trans (min_le_right εI εO)))
  have hnearP := hnear.trans_le (add_le_add le_rfl ((min_le_right _ _).trans (min_le_left εP εS)))
  have hnearS := hnear.trans_le (add_le_add le_rfl ((min_le_right _ _).trans (min_le_right εP εS)))
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.2.le⟩
  by_cases hexception : r.val = 0 ∧ |u| ≤ qs 0
  · have hr : r = 0 := Fin.ext hexception.1
    subst r
    have huq : u < qs 0 := by
      rw [abs_of_nonpos (sub_nonpos.2 ((le_abs_self u).trans hexception.2))] at hdist
      linarith
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
          have hdistI : ρ ≤ qs p.succ - u := by
            rw [abs_of_nonpos (sub_nonpos.2 hleft)] at hdist
            linarith
          obtain ⟨w, hw⟩ := hinner hμ.integrable_id ms qs hm hmin.1 hfull hnearI p t ht u huI hdistI
          exact ⟨.inner p rfl w, hw⟩
      · have huO : u ∈ Icc (qs r) (qExt qs (r.val + 2)) := ⟨hright, hinside.2⟩
        have hdistO : ρ ≤ u - qs r := by rwa [abs_of_nonneg (sub_nonneg.2 hright)] at hdist
        obtain ⟨w, hw⟩ := houter hμ.integrable_id ms qs hm hmin.1 hfull hnearO r t ht u huO hdistO
        exact ⟨.outer w, hw⟩
    · have houtside : u < qExt qs r.val ∨ qExt qs (r.val + 2) < u := by
        by_cases hleft : u < qExt qs r.val
        · exact Or.inl hleft
        · exact Or.inr (lt_of_not_ge (fun hright => hinside ⟨le_of_not_gt hleft, hright⟩))
      obtain ⟨w, hw⟩ := exists_parisiCanonicalTrial_positive_outside_gap hμ hξ ms qs hm hmin r
        ht₀ ht hu houtside hexception
      exact ⟨.canonical w, hw⟩

end SpinGlass
