import SpinGlass.Parisi.Coupled.CoupledMainOffCenter

/-!
# The uniform coupled main estimate

Theorem 14.5.7 follows from the concrete continuous trial cover and
the local quadratic pressure estimates. The tolerance is chosen before
the MIN parameters; the final constant depends on those parameters but
is independent of volume, time, level, overlap and Gaussian realization.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- A strict overlap chain has a positive common radius lying inside
every neighboring interval. This radius may depend on the chosen MIN. -/
theorem exists_parisi_neighbor_radius {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (hchain : ∀ j : ℕ, j < k + 2 → qExt qs j < qExt qs (j + 1)) :
    ∃ a : ℝ, 0 < a ∧ ∀ r : Fin (k + 1), ∀ u : ℝ, |u - qs r| ≤ a →
      u ∈ Icc (qExt qs r.val) (qExt qs (r.val + 2)) := by
  let d (r : Fin (k + 1)) := min (qs r - qExt qs r.val) (qExt qs (r.val + 2) - qs r)
  have hd (r : Fin (k + 1)) : 0 < d r := by
    have hL := hchain r.val (by omega)
    have hR := hchain (r.val + 1) (by omega)
    rw [qExt_succ_of_lt qs r.isLt] at hL
    rw [qExt_succ_of_lt qs r.isLt, show r.val + 1 + 1 = r.val + 2 by omega] at hR
    exact lt_min (sub_pos.2 hL) (sub_pos.2 hR)
  obtain ⟨a, ha, har⟩ := exists_uniform_positive_lower_bound_of_finite d hd
  refine ⟨a, ha, ?_⟩
  intro r u hu
  have hL := (har r).trans (min_le_left (qs r - qExt qs r.val) (qExt qs (r.val + 2) - qs r))
  have hR := (har r).trans (min_le_right (qs r - qExt qs r.val) (qExt qs (r.val + 2) - qs r))
  constructor <;> linarith [(abs_le.1 hu).1, (abs_le.1 hu).2]

/-- Talagrand, Vol. II, Theorem 14.5.7: the original constrained
auxiliary pressure has a uniform quadratic penalty away from each
stationary overlap. Every analytic and physical comparison is concrete. -/
theorem exists_uniform_randomFieldParisiAuxPairPressure_main_estimate
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 0 < N →
      ∀ (Ω : Type) [MeasurableSpace Ω] (Pm : Measure Ω) [IsProbabilityMeasure Pm],
      ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ G₀ : GaussianField (α := Config N) Pm
        (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
      ∀ r : Fin (k + 1), ∀ u ∈ Icc (-1 : ℝ) 1,
      (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
      randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t u G₀ ≤
        2 * parisiInterpolationBracket μh ξ ms qs t - (u - qs r) ^ 2 / K := by
  obtain ⟨εO, hεO, hoff⟩ := exists_uniform_parisiMainTrial_positive_offCenter_gap hμ hξ ht₀
  obtain ⟨εN, hεN, ρ, hρ, hnear⟩ := exists_uniform_randomFieldParisiAuxPairPressure_near_gap hξ hμ ht₀
  obtain ⟨εR, hεR, hroot⟩ := exists_uniform_randomFieldParisiAuxPairPressure_root_gap hξ hμ ht₀
  let ε := min εO (min εN εR)
  refine ⟨ε, lt_min hεO (lt_min hεN hεR), ?_⟩
  intro k ms qs hm hmin hfull hvalue
  have hvalueO := hvalue.trans_le (add_le_add le_rfl (min_le_left εO (min εN εR)))
  have hvalueN := hvalue.trans_le (add_le_add le_rfl ((min_le_right εO (min εN εR)).trans (min_le_left εN εR)))
  have hvalueR := hvalue.trans_le (add_le_add le_rfl ((min_le_right εO (min εN εR)).trans (min_le_right εN εR)))
  obtain ⟨hchain, _⟩ := randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
    ms qs hm hξ hμ hmin
  obtain ⟨a₀, ha₀, hneighbor⟩ := exists_parisi_neighbor_radius qs
    (fun j hj => hchain j (by omega))
  let a := min ρ a₀
  have ha : 0 < a := lt_min hρ ha₀
  obtain ⟨δ, hδ, hfar⟩ := exists_uniform_randomFieldParisiAuxPairPressure_offCenter_gap_of_trialCover
    hμ.integrable_id hξ ms qs hm hmin.1 ht₀ ha (hoff k ms qs hm hmin hfull hvalueO)
  let c := min ((1 - t₀) ^ 2 / 32) (δ / 4)
  have hc : 0 < c := lt_min (div_pos (sq_pos_of_pos (sub_pos.2 ht₀.2)) (by norm_num))
    (div_pos hδ (by norm_num))
  let K := 1 / c
  refine ⟨K, div_pos zero_lt_one hc, ?_⟩
  intro N hN Ω _ Pm _ t ht G₀ r u hu hreach
  have hpenalty : (u - qs r) ^ 2 / K = c * (u - qs r) ^ 2 := by
    dsimp only [K]
    field_simp
  rw [hpenalty]
  have hcost : c * (u - qs r) ^ 2 ≤ (1 - t₀) ^ 2 * (u - qs r) ^ 2 / 32 := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left ((1 - t₀) ^ 2 / 32) (δ / 4))
      (sq_nonneg (u - qs r))
    dsimp only [c]
    nlinarith only [hh]
  by_cases hclose : |u - qs r| ≤ a
  · have hinterval := hneighbor r u (hclose.trans (min_le_right ρ a₀))
    have hsmall := hclose.trans (min_le_left ρ a₀)
    have hnearby := hnear k ms qs hm hmin hfull hvalueN N hN Ω Pm t ht G₀
    rcases le_total u (qs r) with hleft | hright
    · cases r using Fin.cases with
      | zero =>
        have hu0 : 0 ≤ u := by simpa only [Fin.val_zero, qExt_zero] using hinterval.1
        have hb := hroot k ms qs hm hmin hfull hvalueR N hN Ω Pm t ht G₀ u
          (by rwa [abs_of_nonneg hu0]) hreach
        simp only [Fin.val_zero, zero_add]
        nlinarith only [hb, hcost,
          mul_nonneg (sq_nonneg (1 - t₀)) (sq_nonneg (u - qs 0))]
      | succ p =>
        have huI : u ∈ Icc (qs p.castSucc) (qs p.succ) := by
          constructor
          · have hL := hinterval.1
            rw [Fin.val_succ, qExt_succ_of_lt qs (by omega : p.val < k + 1)] at hL
            exact hL
          · exact hleft
        have hdistI : qs p.succ - u ≤ ρ := by
          rw [abs_of_nonpos (sub_nonpos.2 hleft)] at hsmall
          linarith
        have hb := hnearby.1 p u huI hdistI hreach
        simp only [Fin.val_succ, Nat.add_assoc]
        linarith
    · have huO : u ∈ Icc (qs r) (qExt qs (r.val + 2)) := ⟨hright, hinterval.2⟩
      have hdistO : u - qs r ≤ ρ := by rwa [abs_of_nonneg (sub_nonneg.2 hright)] at hsmall
      have hb := hnearby.2 r u huO hdistO hreach
      linarith
  · have hdist : a ≤ |u - qs r| := (lt_of_not_ge hclose).le
    have hb := hfar r t ht u hu hdist N hN Ω Pm G₀ hreach
    have habs : |u - qs r| ≤ 2 := abs_le.2 (by
      constructor <;> linarith [(hmin.1.mem_Icc r).1, (hmin.1.mem_Icc r).2, hu.1, hu.2])
    have hsquare : (u - qs r) ^ 2 ≤ 4 := by nlinarith [(abs_le.1 habs).1, (abs_le.1 habs).2]
    have hcd : c ≤ δ / 4 := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_left hsquare hc.le
    nlinarith only [hb, hcd, hmul]

end SpinGlass
