import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Taylor analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped BigOperators

namespace SpinGlass.Aristotle

noncomputable section

/-- Second-order Taylor control from a Lipschitz derivative, including endpoints. -/
theorem abs_taylor_one_le {F D : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b)
    (hL : 0 ≤ L) (hF : ContinuousOn F (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt F (D x) x)
    (hD : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |D x - D y| ≤ L * |x - y|)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |F y - F x - D x * (y - x)| ≤ L / 2 * (y - x) ^ 2 := by
  set φ : ℝ → ℝ → ℝ := fun s t => s * (F t - F x - D x * (t - x)) - L / 2 * (t - x) ^ 2
  have hφd : ∀ s, ∀ t ∈ Ioo a b, HasDerivAt (φ s) (s * (D t - D x) - L * (t - x)) t := by
    intro s t ht
    have h1 := (((hd t ht).sub_const (F x)).sub
      (((hasDerivAt_id t).sub_const x).const_mul (D x))).const_mul s
    have h2 := (((hasDerivAt_id t).sub_const x).pow 2).const_mul (L / 2)
    convert! h1.sub h2 using 1
    simp; ring
  have hφc : ∀ s, ContinuousOn (φ s) (Icc a b) := fun s =>
    ((hF.sub continuousOn_const).sub (by fun_prop)).const_smul s |>.sub (by fun_prop)
  have hbound : ∀ s, |s| ≤ 1 → ∀ t ∈ Icc a b, |s * (D t - D x)| ≤ L * |t - x| := by
    intro s hs t ht
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hs).trans (hD t ht x hx)
  have key : ∀ s, |s| ≤ 1 → φ s y ≤ φ s x := by
    intro s hs
    rcases le_total x y with hxy | hxy
    · have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
      have hsub' : Ioo x y ⊆ Ioo a b := Ioo_subset_Ioo hx.1 hy.2
      refine antitoneOn_of_deriv_nonpos (convex_Icc x y) ((hφc s).mono hsub) ?_ ?_
        ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
      · rw [interior_Icc]
        exact fun t ht => (hφd s t (hsub' ht)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        rw [(hφd s t (hsub' ht)).deriv]
        have := hbound s hs t (Ioo_subset_Icc_self (hsub' ht))
        rw [abs_of_nonneg (by linarith [ht.1] : 0 ≤ t - x)] at this
        linarith [le_abs_self (s * (D t - D x))]
    · have hsub : Icc y x ⊆ Icc a b := Icc_subset_Icc hy.1 hx.2
      have hsub' : Ioo y x ⊆ Ioo a b := Ioo_subset_Ioo hy.1 hx.2
      refine monotoneOn_of_deriv_nonneg (convex_Icc y x) ((hφc s).mono hsub) ?_ ?_
        ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
      · rw [interior_Icc]
        exact fun t ht => (hφd s t (hsub' ht)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        rw [(hφd s t (hsub' ht)).deriv]
        have := hbound s hs t (Ioo_subset_Icc_self (hsub' ht))
        rw [abs_of_nonpos (by linarith [ht.2] : t - x ≤ 0)] at this
        linarith [neg_abs_le (s * (D t - D x))]
  have h1 := key 1 (by norm_num)
  have h2 := key (-1) (by norm_num)
  simp only [φ, sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- Third-order remainder with a Lipschitz second derivative; no fourth derivative. -/
theorem abs_taylor_two_le {F D E : ℝ → ℝ} {a b L : ℝ}
    (hab : a < b) (hL : 0 ≤ L)
    (hF : ContinuousOn F (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt F (D x) x)
    (he : ∀ x ∈ Ioo a b, HasDerivAt D (E x) x)
    (hE : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |E x - E y| ≤ L * |x - y|)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |F y - F x - D x * (y - x) - E x / 2 * (y - x) ^ 2| ≤
      L / 6 * |y - x| ^ 3 := by
  set g : ℝ → ℝ := fun t => F t - F x - D x * (t - x) - E x / 2 * (t - x) ^ 2
  have hgd : ∀ t ∈ Ioo a b, HasDerivAt g (D t - D x - E x * (t - x)) t := by
    intro t ht
    have h1 := (((hd t ht).sub_const (F x)).sub
      (((hasDerivAt_id t).sub_const x).const_mul (D x)))
    have h2 := (((hasDerivAt_id t).sub_const x).pow 2).const_mul (E x / 2)
    convert! h1.sub h2 using 1
    simp; ring
  have hgc : ContinuousOn g (Icc a b) :=
    ((hF.sub continuousOn_const).sub (by fun_prop)).sub (by fun_prop)
  have hg' : ∀ t ∈ Icc a b, |D t - D x - E x * (t - x)| ≤ L / 2 * (t - x) ^ 2 :=
    fun t ht => abs_taylor_one_le hab.le hL hD he hE hx ht
  have hb : ∀ s, |s| ≤ 1 → ∀ t ∈ Icc a b,
      |s * (D t - D x - E x * (t - x))| ≤ L / 2 * (t - x) ^ 2 := fun s hs t ht => by
    rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) hs).trans (hg' t ht)
  have key : ∀ s, |s| ≤ 1 → s * g y ≤ L / 6 * |y - x| ^ 3 := by
    intro s hs
    rcases le_total x y with hxy | hxy
    · have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
      have hsub' : Ioo x y ⊆ Ioo a b := Ioo_subset_Ioo hx.1 hy.2
      set φ : ℝ → ℝ := fun t => s * g t - L / 6 * (t - x) ^ 3
      have hφd : ∀ t ∈ Ioo x y, HasDerivAt φ
          (s * (D t - D x - E x * (t - x)) - L / 2 * (t - x) ^ 2) t := fun t ht => by
        convert! ((hgd t (hsub' ht)).const_mul s).sub
          ((((hasDerivAt_id t).sub_const x).pow 3).const_mul (L / 6)) using 1
        simp; ring
      have hφc : ContinuousOn φ (Icc x y) :=
        (continuousOn_const.mul (hgc.mono hsub)).sub (by fun_prop)
      have := antitoneOn_of_deriv_nonpos (convex_Icc x y) hφc
        (by
          rw [interior_Icc]
          exact fun t ht => (hφd t ht).differentiableAt.differentiableWithinAt)
        (by
          rw [interior_Icc]; intro t ht
          rw [(hφd t ht).deriv]
          linarith [le_abs_self (s * (D t - D x - E x * (t - x))),
            hb s hs t (hsub (Ioo_subset_Icc_self ht))])
        ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
      simp only [φ, g, sub_self, mul_zero] at this
      rw [abs_of_nonneg (by linarith : 0 ≤ y - x)]
      simpa using this
    · have hsub : Icc y x ⊆ Icc a b := Icc_subset_Icc hy.1 hx.2
      have hsub' : Ioo y x ⊆ Ioo a b := Ioo_subset_Ioo hy.1 hx.2
      set φ : ℝ → ℝ := fun t => s * g t - L / 6 * (x - t) ^ 3
      have hφd : ∀ t ∈ Ioo y x, HasDerivAt φ
          (s * (D t - D x - E x * (t - x)) + L / 2 * (t - x) ^ 2) t := fun t ht => by
        convert! ((hgd t (hsub' ht)).const_mul s).sub
          ((((hasDerivAt_id t).const_sub x).pow 3).const_mul (L / 6)) using 1
        simp; ring
      have hφc : ContinuousOn φ (Icc y x) :=
        (continuousOn_const.mul (hgc.mono hsub)).sub (by fun_prop)
      have := monotoneOn_of_deriv_nonneg (convex_Icc y x) hφc
        (by
          rw [interior_Icc]
          exact fun t ht => (hφd t ht).differentiableAt.differentiableWithinAt)
        (by
          rw [interior_Icc]; intro t ht
          rw [(hφd t ht).deriv]
          linarith [neg_abs_le (s * (D t - D x - E x * (t - x))),
            hb s hs t (hsub (Ioo_subset_Icc_self ht))])
        ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
      simp only [φ, g, sub_self, mul_zero] at this
      rw [abs_of_nonpos (by linarith : y - x ≤ 0), neg_sub]
      simp at this
      exact this
  have h1 := key 1 (by norm_num)
  have h2 := key (-1) (by norm_num)
  rw [abs_le]
  constructor <;> simp only [g] at h1 h2 <;> linarith

end

end SpinGlass.Aristotle
