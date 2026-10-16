import SpinGlass.Parisi.Coupled.CoupledSignedColeHopf

/-!
# Gaussian layers for finite paired recursions

Independent, common and antisymmetric marks are treated by their actual
Gaussian Cole-Hopf operators. Every mass-zero branch is a Gaussian
expectation. Separate unit Lipschitz bounds provide integrability and
propagate through all three kinds of layer.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

def PairUnitLipschitz (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y x' y', |F x' y' - F x y| ≤ |x' - x| + |y' - y|

theorem PairUnitLipschitz.left {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) (y : ℝ) :
    ∀ x x', |F x' y - F x y| ≤ 1 * |x' - x| := by
  intro x x'
  simpa only [sub_self, abs_zero, add_zero, one_mul] using hF x y x' y

theorem PairUnitLipschitz.right {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) (x : ℝ) :
    ∀ y y', |F x y' - F x y| ≤ 1 * |y' - y| := by
  intro y y'
  simpa only [sub_self, abs_zero, zero_add, one_mul] using hF x y x y'

theorem pairUnitLipschitz_of_separate {F : ℝ → ℝ → ℝ}
    (hL : ∀ y x x', |F x' y - F x y| ≤ |x' - x|)
    (hR : ∀ x y y', |F x y' - F x y| ≤ |y' - y|) : PairUnitLipschitz F := by
  intro x y x' y'
  calc
    |F x' y' - F x y| ≤ |F x' y' - F x y'| + |F x y' - F x y| := abs_sub_le _ _ _
    _ ≤ |x' - x| + |y' - y| := add_le_add (hL y' x x') (hR x y y')

theorem PairUnitLipschitz.signed_diagonal {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F)
    {η : ℝ} (hη : |η| = 1) (x y : ℝ) :
    ∀ z z', |F (x + z') (y + η * z') - F (x + z) (y + η * z)| ≤ 2 * |z' - z| := by
  intro z z'
  have h := hF (x + z) (y + η * z) (x + z') (y + η * z')
  rw [add_sub_add_left_eq_sub, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, hη, one_mul] at h
  simpa only [two_mul] using h

noncomputable def independentPairColeHopf (m : ℝ) (v : ℝ≥0) (F : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  coleHopf m v (fun a => coleHopf m v (F a) y) x

noncomputable def correlatedPairColeHopf (η m : ℝ) (v : ℝ≥0) (F : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  coleHopf m v (fun z => F (x + z) (y + η * z)) 0

/-- The independent mass-zero layer is exactly the double
Gaussian expectation, with no exponential normalization. -/
theorem independentPairColeHopf_zero (v : ℝ≥0) (F : ℝ → ℝ → ℝ) (x y : ℝ) :
    independentPairColeHopf 0 v F x y =
      ∫ a, ∫ b, F (x + a) (y + b) ∂gaussianReal 0 v ∂gaussianReal 0 v := by
  simp only [independentPairColeHopf, coleHopf_zero]

theorem exp_mul_correlatedPairColeHopf {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F)
    {η m : ℝ} (hη : |η| = 1) (hm : m ≠ 0) (v : ℝ≥0) (x y : ℝ) :
    Real.exp (m * correlatedPairColeHopf η m v F x y) =
      ∫ z, Real.exp (m * F (x + z) (y + η * z)) ∂gaussianReal 0 v := by
  have hdiag := hF.signed_diagonal hη x y
  simpa only [correlatedPairColeHopf, zero_add] using exp_mul_coleHopf
    (HasLinearGrowth.of_lipschitz hdiag) (lipschitzWith_toNNReal_of_abs_sub_le hdiag).continuous.measurable hm v 0

theorem independentPairColeHopf_inner_lipschitz {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F)
    (m : ℝ) (v : ℝ≥0) (y : ℝ) :
    ∀ a b, |coleHopf m v (F b) y - coleHopf m v (F a) y| ≤ 1 * |b - a| := by
  intro a b
  have ha := hF.right a
  have hb := hF.right b
  apply abs_coleHopf_sub_le_of_sup (HasLinearGrowth.of_lipschitz hb)
    (lipschitzWith_toNNReal_of_abs_sub_le hb).continuous.measurable
    (HasLinearGrowth.of_lipschitz ha) (lipschitzWith_toNNReal_of_abs_sub_le ha).continuous.measurable
    (fun z => ?_) m v y
  simpa only [one_mul] using hF.left z a b

/-- The independent operator is the actual double Gaussian
exponential integral at every nonzero mass. -/
theorem exp_mul_independentPairColeHopf {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F)
    {m : ℝ} (hm : m ≠ 0) (v : ℝ≥0) (x y : ℝ) :
    Real.exp (m * independentPairColeHopf m v F x y) =
      ∫ a, ∫ b, Real.exp (m * F (x + a) (y + b)) ∂gaussianReal 0 v ∂gaussianReal 0 v := by
  have hinner := independentPairColeHopf_inner_lipschitz hF m v y
  rw [independentPairColeHopf, exp_mul_coleHopf (HasLinearGrowth.of_lipschitz hinner)
    (lipschitzWith_toNNReal_of_abs_sub_le hinner).continuous.measurable hm]
  apply integral_congr_ae (.of_forall fun a => ?_)
  exact exp_mul_coleHopf (HasLinearGrowth.of_lipschitz (hF.right (x + a)))
    (lipschitzWith_toNNReal_of_abs_sub_le (hF.right (x + a))).continuous.measurable hm v y

theorem independentPairColeHopf_lipschitz {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F)
    (m : ℝ) (v : ℝ≥0) : PairUnitLipschitz (independentPairColeHopf m v F) := by
  apply pairUnitLipschitz_of_separate
  · intro y x x'
    have hinner := independentPairColeHopf_inner_lipschitz hF m v y
    simpa only [independentPairColeHopf, one_mul] using abs_coleHopf_sub_le_of_lipschitz m
      (lipschitzWith_toNNReal_of_abs_sub_le hinner).continuous.measurable hinner v x x'
  · intro x y y'
    have h₁ := independentPairColeHopf_inner_lipschitz hF m v y
    have h₂ := independentPairColeHopf_inner_lipschitz hF m v y'
    unfold independentPairColeHopf
    apply abs_coleHopf_sub_le_of_sup (HasLinearGrowth.of_lipschitz h₂)
      (lipschitzWith_toNNReal_of_abs_sub_le h₂).continuous.measurable
      (HasLinearGrowth.of_lipschitz h₁) (lipschitzWith_toNNReal_of_abs_sub_le h₁).continuous.measurable
      (fun a => ?_) m v x
    simpa only [one_mul] using abs_coleHopf_sub_le_of_lipschitz m
      (lipschitzWith_toNNReal_of_abs_sub_le (hF.right a)).continuous.measurable (hF.right a) v y y'

theorem correlatedPairColeHopf_lipschitz {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F)
    {η : ℝ} (hη : |η| = 1) (m : ℝ) (v : ℝ≥0) :
    PairUnitLipschitz (correlatedPairColeHopf η m v F) := by
  intro x y x' y'
  have h₁ := hF.signed_diagonal hη x y
  have h₂ := hF.signed_diagonal hη x' y'
  unfold correlatedPairColeHopf
  apply abs_coleHopf_sub_le_of_sup (HasLinearGrowth.of_lipschitz h₂)
    (lipschitzWith_toNNReal_of_abs_sub_le h₂).continuous.measurable
    (HasLinearGrowth.of_lipschitz h₁) (lipschitzWith_toNNReal_of_abs_sub_le h₁).continuous.measurable
    (fun z => ?_) m v 0
  simpa only [add_sub_add_right_eq_sub] using hF (x + z) (y + η * z) (x' + z) (y' + η * z)

theorem pairUnitLipschitz_sum {A : ℝ → ℝ}
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) : PairUnitLipschitz (fun x y => A x + A y) := by
  apply pairUnitLipschitz_of_separate
  · intro y x x'
    simpa only [add_sub_add_right_eq_sub] using hA x x'
  · intro x y y'
    simpa only [add_sub_add_left_eq_sub] using hA y y'

/-- The exact independent factorization (14.373), also at zero
mass, with both marginal values taken from the actual operator. -/
theorem independentPairColeHopf_sum {A : ℝ → ℝ} (hAm : Measurable A)
    {L : ℝ} (hA : ∀ x y, |A y - A x| ≤ L * |y - x|)
    (m : ℝ) (v : ℝ≥0) (x y : ℝ) :
    independentPairColeHopf m v (fun a b => A a + A b) x y = coleHopf m v A x + coleHopf m v A y := by
  have hAg := HasLinearGrowth.of_lipschitz hA
  have hinner (a : ℝ) : coleHopf m v (fun b => A a + A b) y = coleHopf m v A y + A a := by
    simp_rw [add_comm (A a)]
    exact coleHopf_add_const hAg hAm (A a) m v y
  unfold independentPairColeHopf
  simp_rw [hinner, add_comm (coleHopf m v A y)]
  exact coleHopf_add_const hAg hAm _ m v x

theorem independentPairColeHopf_mono {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) (hFG : ∀ x y, F x y ≤ G x y)
    (m : ℝ) (v : ℝ≥0) (x y : ℝ) :
    independentPairColeHopf m v F x y ≤ independentPairColeHopf m v G x y := by
  have h₁ := independentPairColeHopf_inner_lipschitz hF m v y
  have h₂ := independentPairColeHopf_inner_lipschitz hG m v y
  apply coleHopf_mono (HasLinearGrowth.of_lipschitz h₁)
    (lipschitzWith_toNNReal_of_abs_sub_le h₁).continuous.measurable
    (HasLinearGrowth.of_lipschitz h₂) (lipschitzWith_toNNReal_of_abs_sub_le h₂).continuous.measurable
    (fun a => ?_) m v x
  exact coleHopf_mono (HasLinearGrowth.of_lipschitz (hF.right a))
    (lipschitzWith_toNNReal_of_abs_sub_le (hF.right a)).continuous.measurable
    (HasLinearGrowth.of_lipschitz (hG.right a))
    (lipschitzWith_toNNReal_of_abs_sub_le (hG.right a)).continuous.measurable (hFG a) m v y

theorem correlatedPairColeHopf_mono {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) (hFG : ∀ x y, F x y ≤ G x y)
    {η : ℝ} (hη : |η| = 1) (m : ℝ) (v : ℝ≥0) (x y : ℝ) :
    correlatedPairColeHopf η m v F x y ≤ correlatedPairColeHopf η m v G x y := by
  have h₁ := hF.signed_diagonal hη x y
  have h₂ := hG.signed_diagonal hη x y
  exact coleHopf_mono (HasLinearGrowth.of_lipschitz h₁)
    (lipschitzWith_toNNReal_of_abs_sub_le h₁).continuous.measurable
    (HasLinearGrowth.of_lipschitz h₂) (lipschitzWith_toNNReal_of_abs_sub_le h₂).continuous.measurable
    (fun _z => hFG _ _) m v 0

theorem independentPairColeHopf_lt {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) (hFG : ∀ x y, F x y < G x y)
    {m : ℝ} (hm : 0 ≤ m) (v : ℝ≥0) (x y : ℝ) :
    independentPairColeHopf m v F x y < independentPairColeHopf m v G x y := by
  apply coleHopf_lt_of_forall_lt (independentPairColeHopf_inner_lipschitz hF m v y)
    (independentPairColeHopf_inner_lipschitz hG m v y) (fun a => ?_) hm v x
  exact coleHopf_lt_of_forall_lt (hF.right a) (hG.right a) (hFG a) hm v y

theorem correlatedPairColeHopf_lt {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) (hFG : ∀ x y, F x y < G x y)
    {η : ℝ} (hη : |η| = 1) {m : ℝ} (hm : 0 ≤ m) (v : ℝ≥0) (x y : ℝ) :
    correlatedPairColeHopf η m v F x y < correlatedPairColeHopf η m v G x y :=
  coleHopf_lt_of_forall_lt (hF.signed_diagonal hη x y) (hG.signed_diagonal hη x y)
    (fun z => hFG _ _) hm v 0

end SpinGlass
