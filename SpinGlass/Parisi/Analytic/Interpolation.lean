import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Interpolation analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped BigOperators

namespace SpinGlass.Aristotle

noncomputable section

/-! ## Interpolation, endpoint passage, and approximation transfer

Search tag: `PARISI_LB_ENDPOINT`. Keywords: Gronwall, differential inequality,
time cutoff, terminal time, eventual epsilon lower bound, truncation transfer.

Consumers: Theorem 14.5.4, (14.109), and the eventual lower-bound capstone.
Differentiability is only required at interior times. Endpoint continuity is
explicit. In the eventual statements all time points use the same volume threshold.
-/

/-- Gronwall estimate for an interpolation gap starting at zero.
Analytic input for Theorem 14.5.4 and the eventual uniform estimate below. -/
theorem gronwall_zero_initial {f D : ℝ → ℝ} {T K ε : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hc : ContinuousOn f (Icc (0 : ℝ) T)) (hzero : f 0 = 0)
    (hd : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt f (D t) t)
    (hineq : ∀ t ∈ Ioo (0 : ℝ) T, D t ≤ K * (f t + ε)) :
    ∀ t ∈ Icc (0 : ℝ) T, f t ≤ ε * (Real.exp (K * t) - 1) := by
  set g : ℝ → ℝ := fun t => (f t + ε) * Real.exp (-(K * t))
  have hg : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt g ((D t - K * (f t + ε)) * Real.exp (-(K * t))) t := by
    intro t ht
    have h2 : HasDerivAt (fun s => -(K * s)) (-K) t := by
      convert! ((hasDerivAt_id t).const_mul K).neg using 1 <;> simp
    convert! ((hd t ht).add_const ε).mul h2.exp using 1
    ring
  have hanti : AntitoneOn g (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) ?_ ?_ ?_
    · exact (hc.add continuousOn_const).mul (by fun_prop)
    · rw [interior_Icc]
      exact fun t ht => (hg t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hg t ht).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hineq t ht]) (Real.exp_nonneg _)
  intro t ht
  have h := hanti ⟨le_rfl, hT⟩ ht ht.1
  simp only [g, hzero, zero_add, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
  have := (le_div_iff₀ (Real.exp_pos _)).2 h
  rw [Real.exp_neg, div_inv_eq_mul] at this
  linarith

/-- Constant K is chosen before ε; thresholds may depend on ε. -/
theorem eventually_uniform_small_of_differential_inequality
    {f D : ℕ → ℝ → ℝ} {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hc : ∀ n, ContinuousOn (f n) (Icc (0 : ℝ) T))
    (hzero : ∀ n, f n 0 = 0)
    (hd : ∀ n t, t ∈ Ioo (0 : ℝ) T → HasDerivAt (f n) (D n t) t)
    (hineq : ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Ioo (0 : ℝ) T,
      D n t ≤ K * (f n t + ε)) :
    ∀ δ > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T, f n t ≤ δ := by
  intro δ hδ
  have hE := Real.exp_pos (K * T)
  filter_upwards [hineq (δ / Real.exp (K * T)) (by positivity)] with n hn t ht
  refine (gronwall_zero_initial hT hK (by positivity) (hc n) (hzero n) (hd n) hn t ht).trans ?_
  have : Real.exp (K * t) ≤ Real.exp (K * T) := Real.exp_le_exp.2 (by nlinarith [ht.2])
  calc δ / Real.exp (K * T) * (Real.exp (K * t) - 1)
      ≤ δ / Real.exp (K * T) * Real.exp (K * T) := by gcongr; linarith
    _ = δ := div_mul_cancel₀ _ hE.ne'

/-- Coarse comparison on the final time interval, including the endpoint t=1. -/
theorem endpoint_lower_of_derivative_bound {φ D : ℝ → ℝ} {t M : ℝ}
    (ht : t < 1) (hc : ContinuousOn φ (Icc t 1))
    (hd : ∀ s ∈ Ioo t 1, HasDerivAt φ (D s) s)
    (hbound : ∀ s ∈ Ioo t 1, -M ≤ D s) :
    φ t - M * (1 - t) ≤ φ 1 := by
  have hder : ∀ s ∈ Ioo t 1, HasDerivAt (fun s => φ s + M * s) (D s + M) s := fun s hs => by
    convert! (hd s hs).add ((hasDerivAt_id s).const_mul M) using 1 <;> simp
  have hmono : MonotoneOn (fun s => φ s + M * s) (Icc t 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc t 1) (hc.add (by fun_prop)) ?_ ?_
    · rw [interior_Icc]
      exact fun s hs => (hder s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hder s hs).deriv]
      linarith [hbound s hs]
  have := hmono ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht.le
  simp only at this
  linarith

/-- Choose the cutoff before the approximating parameters and the volume threshold. -/
theorem eventual_lower_of_cutoff_estimates {p : ℕ → ℝ} {P M : ℝ}
    (hM : 0 ≤ M)
    (hcut : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ δ > 0,
      ∀ᶠ n in atTop, P - M * (1 - t) - δ ≤ p n) :
    ∀ ε > 0, ∀ᶠ n in atTop, P - ε ≤ p n := by
  intro ε hε
  set r := min (1 / 2) (ε / (2 * (M + 1)))
  have hr : 0 < r := by positivity
  have hr1 : r ≤ 1 / 2 := min_le_left _ _
  have hMr : M * r ≤ ε / 2 := by
    calc M * r ≤ (M + 1) * (ε / (2 * (M + 1))) := by
          gcongr
          · linarith
          · exact min_le_right _ _
      _ = ε / 2 := by field_simp
  filter_upwards [hcut (1 - r) ⟨by linarith, by linarith⟩ (ε / 2) (by positivity)] with n hn
  rw [sub_sub_cancel] at hn
  linarith

/-- Transfer bounded-field lower bounds through uniform truncation errors.
The approximation index is fixed before taking volume large. -/
theorem eventual_lower_of_uniform_approximation
    {p : ℕ → ℝ} {P : ℝ} {pApprox : ℕ → ℕ → ℝ} {PApprox e : ℕ → ℝ}
    (he : ∀ j, 0 ≤ e j) (hlim : Tendsto e atTop (𝓝 0))
    (hp : ∀ j n, |p n - pApprox j n| ≤ e j)
    (hP : ∀ j, |P - PApprox j| ≤ e j)
    (happrox : ∀ j, ∀ ε > 0, ∀ᶠ n in atTop, PApprox j - ε ≤ pApprox j n) :
    ∀ ε > 0, ∀ᶠ n in atTop, P - ε ≤ p n := by
  intro ε hε
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds (by positivity : 0 < ε / 3))).exists
  filter_upwards [happrox j (ε / 3) (by positivity)] with n hn
  linarith [(abs_le.1 (hp j n)).1, (abs_le.1 (hP j)).2]

end

end SpinGlass.Aristotle
