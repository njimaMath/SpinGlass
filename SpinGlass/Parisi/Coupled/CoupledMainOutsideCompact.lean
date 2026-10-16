import SpinGlass.Parisi.Coupled.CoupledCanonicalTrialComparison
import SpinGlass.Parisi.Coupled.CoupledCanonicalZeroTime
import SpinGlass.Parisi.Coupled.CoupledCanonicalClosedGap
import SpinGlass.Parisi.Coupled.CoupledCompactWitness

/-!
# Uniform physical pressure gaps on compact outside regions

At each point a concrete canonical trial and coupling give a positive
scalar gap. Fixed trials bound every realized overlap, so a finite cover
of any compact outside region gives one positive gap before volume and
Gaussian realization. The zero-time boundary is included by its concrete
stationary quadratic coupling witness. The initial exception and the
neighboring-interval boundaries remain separate main-estimate cases.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

structure ParisiCanonicalTrial {k : ℕ} (qs : Fin (k + 1) → ℝ) where
  negative : Bool
  split : Fin (k + 2)
  magnitude : ℝ
  admissible : magnitude ∈ Icc (qExt qs split.val) (qExt qs (split.val + 1))
  coupling : ℝ

theorem ParisiCanonicalTrial.magnitude_mem_Icc {k : ℕ} {qs : Fin (k + 1) → ℝ}
    (w : ParisiCanonicalTrial qs) (hq : ParisiQAdmissible qs) : w.magnitude ∈ Icc (0 : ℝ) 1 :=
  ⟨(qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 w.split.val).1.trans w.admissible.1,
    w.admissible.2.trans (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 (w.split.val + 1)).2⟩

theorem exists_parisiCanonicalSplit_interval_closed {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    ∃ p : Fin (k + 2), v ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)) := by
  by_cases hv0 : v = 0
  · subst v
    refine ⟨0, ?_⟩
    simp only [Fin.val_zero, qExt_zero, zero_add, qExt_succ_of_lt qs (by omega : 0 < k + 1)]
    exact ⟨le_rfl, hq.2.1⟩
  · obtain ⟨p, hp⟩ := exists_parisiCanonicalSplit_interval qs
      ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0), hv.2⟩
    exact ⟨p, hp.1.le, hp.2⟩

/-- A concrete trial gives a positive physical scalar witness at
every outside point, including time zero, before any volume is chosen. -/
theorem exists_parisiCanonicalTrial_positive_outside_gap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) (r : Fin (k + 1))
    {t₀ t u : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) t₀)
    (hu : u ∈ Icc (-1 : ℝ) 1)
    (hfar : u < qExt qs r.val ∨ qExt qs (r.val + 2) < u)
    (hexception : ¬(r.val = 0 ∧ |u| ≤ qs 0)) :
    ∃ w : ParisiCanonicalTrial qs,
      0 < parisiCanonicalTrialGap μh ξ ms qs w.negative r w.split w.magnitude w.coupling t u := by
  classical
  have hq := hmin.1
  have hsign : (if decide (u < 0) then -|u| else |u|) = u := by
    by_cases hn : u < 0
    · simp [hn, abs_of_neg hn]
    · simp [hn, abs_of_nonneg (le_of_not_gt hn)]
  by_cases ht0 : t = 0
  · subst t
    obtain ⟨p, hp⟩ := exists_parisiCanonicalSplit_interval_closed qs hq
      ⟨abs_nonneg u, abs_le.2 hu⟩
    have hL : qExt qs r.val ≤ qs r := by
      simpa only [qExt_succ_of_lt qs r.isLt] using
        hq.monotone_qExt (show r.val ≤ r.val + 1 by omega)
    have hR : qs r ≤ qExt qs (r.val + 2) := by
      simpa only [qExt_succ_of_lt qs r.isLt] using
        hq.monotone_qExt (show r.val + 1 ≤ r.val + 2 by omega)
    have hne : u - qs r ≠ 0 := sub_ne_zero.2 (by
      rcases hfar with hleft | hright
      · exact (hleft.trans_le hL).ne
      · exact (hR.trans_lt hright).ne')
    have hg := parisiCanonicalCouplingGap_zero_time_ge_quadratic hμ hξ ms qs hm hmin
      (decide (u < 0)) r p |u|
    rw [hsign] at hg
    have hpos : 0 < parisiCanonicalCouplingGap μh ξ ms qs (decide (u < 0)) r p 0 |u|
        (u - qs r) := (div_pos (sq_pos_of_ne_zero hne) (by norm_num : (0 : ℝ) < 2)).trans_le hg
    refine ⟨⟨decide (u < 0), p, |u|, hp, u - qs r⟩, ?_⟩
    have he := parisiCanonicalTrialGap_at_trial_eq μh ξ ms qs (decide (u < 0)) r p |u|
      (u - qs r) 0
    rw [hsign] at he
    change 0 < parisiCanonicalTrialGap μh ξ ms qs (decide (u < 0)) r p |u| (u - qs r) 0 u
    rw [he]
    exact hpos
  · have hchain := (randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
      ms qs hm hξ hμ hmin).1
    have hq0 : 0 < qs 0 := by
      have hh := hchain 0 (by omega)
      rw [qExt_zero, zero_add, qExt_succ_of_lt qs (by omega : 0 < k + 1)] at hh
      convert hh using 1
      congr 1
    have hq1 : qs (Fin.last k) < 1 := by
      have hh := hchain (k + 1) (by omega)
      rw [qExt_add_two, qExt_succ_of_lt qs (by omega : k < k + 1)] at hh
      convert hh using 1
      congr 1
    have ht' : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2.trans_lt ht₀.2⟩
    obtain ⟨p, hp, hg⟩ := exists_randomFieldPairColeHopfListValue_parisiCanonical_outside_gap
      hμ.integrable_id hξ ms qs hm hq hq0 hq1 r ht' hu hfar hexception
    refine ⟨⟨decide (u < 0), p, |u|, hp, 0⟩, ?_⟩
    have he := parisiCanonicalTrialGap_at_trial_eq μh ξ ms qs (decide (u < 0)) r p |u| 0 t
    rw [hsign] at he
    change 0 < parisiCanonicalTrialGap μh ξ ms qs (decide (u < 0)) r p |u| 0 t u
    rw [he, parisiCanonicalCouplingGap_zero_eq]
    exact sub_pos.2 hg

/-- The outside comparison is uniform on any compact region satisfying
the stated outside and initial-exception conditions. Time zero is included;
the gap precedes every volume and Gaussian probability realization. -/
theorem exists_uniform_randomFieldParisiAuxPairPressure_outside_compact_gap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) (r : Fin (k + 1))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) (s : Set (ℝ × ℝ)) (hs : IsCompact s)
    (ht : ∀ x ∈ s, x.1 ∈ Icc (0 : ℝ) t₀) (hu : ∀ x ∈ s, x.2 ∈ Icc (-1 : ℝ) 1)
    (hfar : ∀ x ∈ s, x.2 < qExt qs r.val ∨ qExt qs (r.val + 2) < x.2)
    (hexception : ∀ x ∈ s, ¬(r.val = 0 ∧ |x.2| ≤ qs 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t u : ℝ, (t, u) ∈ s →
      ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
        (Pm : Measure Ω) [IsProbabilityMeasure Pm],
      ∀ G₀ : GaussianField (α := Config N) Pm
        (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
      (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
      randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t u G₀ ≤
        2 * parisiInterpolationBracket μh ξ ms qs t - δ := by
  let g := fun w : ParisiCanonicalTrial qs => fun x : ℝ × ℝ =>
    parisiCanonicalTrialGap μh ξ ms qs w.negative r w.split w.magnitude w.coupling x.1 x.2
  have hc : ∀ w, ContinuousOn (g w) s := fun w =>
    (continuous_parisiCanonicalTrialGap_time_overlap hμ.integrable_id hξ ms qs w.negative r w.split
      (w.magnitude_mem_Icc hmin.1) w.coupling).continuousOn
  have hp : ∀ x ∈ s, ∃ w, 0 < g w x := fun x hx =>
    exists_parisiCanonicalTrial_positive_outside_gap hμ hξ ms qs hm hmin r ht₀
      (ht x hx) (hu x hx) (hfar x hx) (hexception x hx)
  obtain ⟨δ, hδ, hcover⟩ := exists_uniform_positive_continuous_witness hs g hc hp
  refine ⟨δ, hδ, ?_⟩
  intro t u htu N hN Ω _ Pm _ G₀ hreach
  obtain ⟨w, hw⟩ := hcover (t, u) htu
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨(ht (t, u) htu).1, (ht (t, u) htu).2.trans ht₀.2.le⟩
  have hb := randomFieldParisiAuxPairPressure_le_canonicalTrialGap hμ.integrable_id hN hξ ms qs hm
    hmin.1 w.negative r w.split u ht01 w.admissible w.coupling G₀ hreach
  dsimp only [g] at hw
  linarith

end SpinGlass
