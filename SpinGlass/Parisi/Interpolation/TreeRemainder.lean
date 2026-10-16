import SpinGlass.Parisi.Interpolation.ProfileRemainder
import SpinGlass.Parisi.Interpolation.WeightedIntegral
import SpinGlass.Parisi.Guerra.GuerraRSB

/-!
# The exact finite-tree Guerra remainder

The profile defect is retained in the weighted covariance identity. Its
nonnegativity and curvature bound hold for both signs of the physical
overlap and are uniform in the number of branches.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N : ℕ} {A : Type*} [Fintype A]

noncomputable def weightedTreeProfileRemainder
    (ξ : ℝ → ℝ) (qt : A → A → ℝ) (wt : Config N × A → ℝ)
    (H : FiniteGibbs.EnergySpace (Config N × A)) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, ∑ y, wGibbs wt H x * wGibbs wt H y *
    parisiProfileRemainder ξ (overlap N x.1 y.1) (qt x.2 y.2)

theorem continuous_weightedTreeProfileRemainder
    (ξ : ℝ → ℝ) (qt : A → A → ℝ)
    (wt : Config N × A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0) :
    Continuous (weightedTreeProfileRemainder ξ qt wt) := by
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro x _
  apply continuous_finsetSum
  intro y _
  exact ((continuous_wGibbs wt hwt hne x).mul
    (continuous_wGibbs wt hwt hne y)).mul_const _

/-- The finite weighted form of the exact remainder in (14.108). -/
theorem wGuerraTrace_tree_eq_sub_remainder
    (hN : 0 < N) (ξ : ℝ → ℝ) (qt : A → A → ℝ) (qbar : ℝ)
    (hqt : ∀ α, qt α α = qbar) (wt : Config N × A → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (hne : ∃ x, wt x ≠ 0) (H : FiniteGibbs.EnergySpace (Config N × A)) :
    wGuerraTrace wt (modelKernel N ξ) (treeKernel N ξ qt) N H =
      treeBoundIntegrand wt (ξ 1 - deriv ξ qbar) (fun x y => parisiTheta ξ (qt x.2 y.2)) H -
        weightedTreeProfileRemainder ξ qt wt H := by
  rw [wGuerraTrace_tree_eq hN ξ qt qbar hqt wt hwt hne H]
  have he (x y : Config N × A) : wGibbs wt H x * wGibbs wt H y *
      (ξ (overlap N x.1 y.1) - overlap N x.1 y.1 * deriv ξ (qt x.2 y.2)) =
      wGibbs wt H x * wGibbs wt H y *
        parisiProfileRemainder ξ (overlap N x.1 y.1) (qt x.2 y.2) -
      wGibbs wt H x * wGibbs wt H y * parisiTheta ξ (qt x.2 y.2) := by
    unfold parisiProfileRemainder parisiTheta
    ring
  simp_rw [he, Finset.sum_sub_distrib]
  unfold treeBoundIntegrand weightedTreeProfileRemainder
  ring

theorem weightedTreeProfileRemainder_nonneg
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) (qt : A → A → ℝ)
    (hq : ∀ α γ, qt α γ ∈ Icc (0 : ℝ) 1)
    (wt : Config N × A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (H : FiniteGibbs.EnergySpace (Config N × A)) :
    0 ≤ weightedTreeProfileRemainder ξ qt wt H := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (mul_nonneg (wGibbs_nonneg wt hwt hne H x)
    (wGibbs_nonneg wt hwt hne H y))
    (hξ.profileRemainder_bounds (abs_le.1 (abs_overlap_le_one N x.1 y.1))
      ⟨by linarith [(hq x.2 y.2).1], (hq x.2 y.2).2⟩).1

/-- A single curvature bound works for every finite truncation and every
realized field, disorder and nonnegative family of weights. -/
theorem weightedTreeProfileRemainder_le_curvature
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) (qt : A → A → ℝ)
    (hq : ∀ α γ, qt α γ ∈ Icc (0 : ℝ) 1)
    (wt : Config N × A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (H : FiniteGibbs.EnergySpace (Config N × A)) :
    weightedTreeProfileRemainder ξ qt wt H ≤ deriv (deriv ξ) 1 := by
  have hL := (hξ.second_pos 1 ⟨zero_le_one, le_rfl⟩ one_ne_zero).le
  have hs := sum_wGibbs wt hwt hne H
  have hp (x y : Config N × A) :
      parisiProfileRemainder ξ (overlap N x.1 y.1) (qt x.2 y.2) ≤
        2 * deriv (deriv ξ) 1 := by
    have hu := abs_le.1 (abs_overlap_le_one N x.1 y.1)
    have hq' := hq x.2 y.2
    have habs : |overlap N x.1 y.1 - qt x.2 y.2| ≤ 2 :=
      abs_le.2 ⟨by linarith [hu.1, hq'.2], by linarith [hu.2, hq'.1]⟩
    have hsq : (overlap N x.1 y.1 - qt x.2 y.2) ^ 2 ≤ 4 := by
      nlinarith only [sq_abs (overlap N x.1 y.1 - qt x.2 y.2),
        sq_nonneg (|overlap N x.1 y.1 - qt x.2 y.2| - 2),
        mul_nonneg (sub_nonneg.2 habs)
          (add_nonneg (abs_nonneg (overlap N x.1 y.1 - qt x.2 y.2))
            (by norm_num : (0 : ℝ) ≤ 2))]
    calc
      _ ≤ deriv (deriv ξ) 1 / 2 * (overlap N x.1 y.1 - qt x.2 y.2) ^ 2 :=
        (hξ.profileRemainder_bounds hu ⟨by linarith [hq'.1], hq'.2⟩).2
      _ ≤ deriv (deriv ξ) 1 / 2 * 4 :=
        mul_le_mul_of_nonneg_left hsq (div_nonneg hL (by norm_num))
      _ = _ := by ring
  have hh : (∑ x, ∑ y, wGibbs wt H x * wGibbs wt H y *
      parisiProfileRemainder ξ (overlap N x.1 y.1) (qt x.2 y.2)) ≤
      ∑ x, ∑ y, wGibbs wt H x * wGibbs wt H y * (2 * deriv (deriv ξ) 1) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (hp x y) (mul_nonneg (wGibbs_nonneg wt hwt hne H x)
        (wGibbs_nonneg wt hwt hne H y))
  have he : (∑ x, ∑ y, wGibbs wt H x * wGibbs wt H y * (2 * deriv (deriv ξ) 1)) =
      2 * deriv (deriv ξ) 1 := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, hs, mul_one]
    rw [hs, one_mul]
  rw [he] at hh
  have := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  unfold weightedTreeProfileRemainder
  linarith only [this]

/-- Talagrand's assumptions identify the actual Gaussian tree covariance;
no separate differentiability or derivative-at-zero assumption is needed. -/
theorem treeFieldKernel_parisi_eq_treeKernel
    {k M : ℕ} (hN : 0 < N) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) :
    treeFieldKernel N k M (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1)) =
      treeKernel N ξ (treeOverlap qs) := by
  have hzero : deriv ξ 0 = 0 := by
    have hd := hξ.hasDeriv 0 (by norm_num)
    have hn : HasDerivAt (fun x : ℝ => -x) (-1) 0 := by
      convert (hasDerivAt_id (0 : ℝ)).neg using 1 <;> rfl
    have hdneg : HasDerivAt ξ (deriv ξ 0) (-0) := by simpa only [neg_zero] using hd
    have hneg := hdneg.comp 0 hn
    simp only [Function.comp_def, mul_neg_one] at hneg
    rw [show (fun x => ξ (-x)) = ξ from funext hξ.even] at hneg
    have hh := hneg.unique hd
    linarith
  apply treeFieldKernel_eq_treeKernel hN ξ qs _ hzero
  intro r hr
  exact hξ.strictMonoOn_deriv.monotoneOn
    (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 r)
    (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 (r + 1))
    (qExt_le_succ hq.monotone hq.2.1 hq.2.2 hr)

end SpinGlass
