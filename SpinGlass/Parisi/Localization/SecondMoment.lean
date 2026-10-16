import SpinGlass.Parisi.Localization.ParisiLocalization
import SpinGlass.Parisi.Localization.BranchMassPartition

/-!
# Localized overlap second moments

Exact meeting-mass normalization converts bad-event localization into a
bound for the sum of the physical overlap second moments. The constant
is chosen before the requested accuracy and works uniformly in time.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N k : ℕ}

/-- The joint second moment of the overlap error at a meeting level. -/
noncomputable def parisiBranchSecondMoment (N : ℕ) (μh : Measure ℝ) (ξ : ℝ → ℝ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (t : ℝ) : ℝ :=
  ∑ u ∈ parisiOverlapValues N,
    (u - qs r) ^ 2 * parisiBranchMeetingMass N μh ξ ms qs r t u

theorem parisiBadOverlapMass_antitone
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (t : ℝ) :
    Antitone (parisiBadOverlapMass N μh ξ ms qs r t) := by
  classical
  intro a b hab
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro u hu
    obtain ⟨hu, hb⟩ := Finset.mem_filter.1 hu
    exact Finset.mem_filter.2 ⟨hu, hab.trans hb⟩
  · intro u _ _
    exact parisiBranchMeetingMass_nonneg μh ξ ms qs hm r t u

/-- The second moment is controlled by the good-event threshold and
four times the bad joint mass. -/
theorem parisiBranchSecondMoment_le
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) (r : Fin (k + 1)) (t : ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    parisiBranchSecondMoment N μh ξ ms qs r t ≤
      a * (mExt ms (r.val + 1) - mExt ms r.val) +
        4 * parisiBadOverlapMass N μh ξ ms qs r t a := by
  classical
  let p := parisiBranchMeetingMass N μh ξ ms qs r t
  have hp (u) : 0 ≤ p u := parisiBranchMeetingMass_nonneg μh ξ ms qs hm r t u
  have hb (u : ℝ) (hu : u ∈ parisiOverlapValues N) :
      (u - qs r) ^ 2 * p u ≤ a * p u + if a ≤ (u - qs r) ^ 2 then 4 * p u else 0 := by
    by_cases hbad : a ≤ (u - qs r) ^ 2
    · rw [ite_eq_left hbad]
      have hs : (u - qs r) ^ 2 ≤ 4 := by
        obtain ⟨hu0, hu1⟩ := parisiOverlapValues_mem_Icc hu
        obtain ⟨hq0, hq1⟩ := hq.mem_Icc r
        nlinarith [sq_nonneg (u - qs r + 2), sq_nonneg (u - qs r - 2)]
      have hh := mul_le_mul_of_nonneg_right hs (hp u)
      nlinarith only [hh, mul_nonneg ha (hp u)]
    · rw [ite_eq_right hbad, add_zero]
      exact mul_le_mul_of_nonneg_right (le_of_not_ge hbad) (hp u)
  calc
    _ ≤ ∑ u ∈ parisiOverlapValues N,
        (a * p u + if a ≤ (u - qs r) ^ 2 then 4 * p u else 0) := Finset.sum_le_sum hb
    _ = a * (∑ u ∈ parisiOverlapValues N, p u) +
        4 * parisiBadOverlapMass N μh ξ ms qs r t a := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter, ← Finset.mul_sum]
      rfl
    _ = _ := by rw [sum_parisiBranchMeetingMass_eq_mass_increment μh ξ ms qs hm r t]

theorem sum_parisi_mass_increments (ms : Fin k → ℝ) :
    (∑ r : Fin (k + 1), (mExt ms (r.val + 1) - mExt ms r.val)) = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => mExt ms (j + 1) - mExt ms j), Finset.sum_range_sub]
  simp only [mExt_eq_one_of_le ms le_rfl, mExt_zero, sub_zero]

/-- A uniform coarse bound, independent of localization accuracy. -/
theorem parisiBranchSecondMoment_le_four_mul_increment
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) (r : Fin (k + 1)) (t : ℝ) :
    parisiBranchSecondMoment N μh ξ ms qs r t ≤
      4 * (mExt ms (r.val + 1) - mExt ms r.val) := by
  calc
    _ ≤ ∑ u ∈ parisiOverlapValues N, 4 * parisiBranchMeetingMass N μh ξ ms qs r t u := by
      apply Finset.sum_le_sum
      intro u hu
      apply mul_le_mul_of_nonneg_right _ (parisiBranchMeetingMass_nonneg μh ξ ms qs hm r t u)
      obtain ⟨hu0, hu1⟩ := parisiOverlapValues_mem_Icc hu
      obtain ⟨hq0, hq1⟩ := hq.mem_Icc r
      nlinarith [sq_nonneg (u - qs r + 2), sq_nonneg (u - qs r - 2)]
    _ = _ := by
      rw [← Finset.mul_sum, sum_parisiBranchMeetingMass_eq_mass_increment μh ξ ms qs hm r t]

theorem sum_parisiBranchSecondMoment_le_four
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) (t : ℝ) :
    (∑ r : Fin (k + 1), parisiBranchSecondMoment N μh ξ ms qs r t) ≤ 4 := by
  calc
    _ ≤ ∑ r : Fin (k + 1), 4 * (mExt ms (r.val + 1) - mExt ms r.val) :=
      Finset.sum_le_sum fun r _ =>
        parisiBranchSecondMoment_le_four_mul_increment μh ξ ms qs hm hq r t
    _ = 4 := by rw [← Finset.mul_sum, sum_parisi_mass_increments, mul_one]

/-- Summing over meeting levels costs only the sum of bad masses,
since the exact level masses telescope to one. -/
theorem sum_parisiBranchSecondMoment_le
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) (t : ℝ) {a η : ℝ} (ha : 0 ≤ a)
    (hbad : ∀ r : Fin (k + 1), parisiBadOverlapMass N μh ξ ms qs r t a ≤ η) :
    (∑ r : Fin (k + 1), parisiBranchSecondMoment N μh ξ ms qs r t) ≤
      a + 4 * (k + 1 : ℕ) * η := by
  calc
    _ ≤ ∑ r : Fin (k + 1),
        (a * (mExt ms (r.val + 1) - mExt ms r.val) + 4 * η) := by
      apply Finset.sum_le_sum
      intro r _
      exact (parisiBranchSecondMoment_le μh ξ ms qs hm hq r t ha).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hbad r) (by norm_num)))
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_parisi_mass_increments]
      simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The concrete second-moment estimate needed in the interpolation
remainder. A positive part permits use before the Guerra sign has been
identified; no extra pressure-ordering hypothesis is imposed. -/
theorem eventually_sum_parisiBranchSecondMoment_le_of_localization
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t₀ K : ℝ} (hK : 0 < K)
    (hloc : ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc (0 : ℝ) t₀, ∀ r : Fin (k + 1),
      parisiBadOverlapMass N μh ξ ms qs r t
        (K * (parisiInterpolationBracket μh ξ ms qs t -
          parisiInterpolationPressure N μh ξ ms qs t + ε)) ≤ ε) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc (0 : ℝ) t₀,
      (∑ r : Fin (k + 1), parisiBranchSecondMoment N μh ξ ms qs r t) ≤
        (K + 1) * (max (parisiInterpolationBracket μh ξ ms qs t -
          parisiInterpolationPressure N μh ξ ms qs t) 0 + ε) := by
  intro ε hε
  let η := ε / (4 * (k + 1 : ℕ))
  have hden : (0 : ℝ) < 4 * (k + 1 : ℕ) := by positivity
  have hη : 0 < η := div_pos hε hden
  have hηε : η ≤ ε := by
    apply div_le_self hε.le
    norm_cast
    omega
  filter_upwards [hloc η hη] with N hN t ht
  let f := parisiInterpolationBracket μh ξ ms qs t - parisiInterpolationPressure N μh ξ ms qs t
  let a := K * (max f 0 + ε)
  have ha : 0 ≤ a := mul_nonneg hK.le (add_nonneg (le_max_right _ _) hε.le)
  have hbad (r : Fin (k + 1)) : parisiBadOverlapMass N μh ξ ms qs r t a ≤ η := by
    apply (parisiBadOverlapMass_antitone μh ξ ms qs hm r t ?_).trans (hN t ht r)
    apply mul_le_mul_of_nonneg_left _ hK.le
    exact add_le_add (le_max_left _ _) hηε
  have hh := sum_parisiBranchSecondMoment_le μh ξ ms qs hm hq t ha hbad
  have he : 4 * (k + 1 : ℕ) * η = ε := by
    dsimp only [η]
    field_simp
  rw [he] at hh
  dsimp only [a] at hh
  change _ ≤ (K + 1) * (max f 0 + ε)
  linarith only [hh, le_max_right f 0]

end SpinGlass
