import SpinGlass.Parisi.Coupled.CoupledPairColeHopf
import SpinGlass.Parisi.Coupled.CoupledColeHopfEquality

/-!
# Equality and strict comparison for Gaussian paired layers

Nonzero independent marks have full support in both fields. Common
and antisymmetric marks have full support along their actual diagonal.
Equality therefore propagates through the same sets used in (14.378),
without a positive-mass restriction on the preceding layer.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

theorem independentPairColeHopf_eq_implies_eq {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) (hFG : ∀ x y, F x y ≤ G x y)
    {m : ℝ} (hm : 0 ≤ m) {v : ℝ≥0} (hv : v ≠ 0) (x y : ℝ)
    (he : independentPairColeHopf m v F x y = independentPairColeHopf m v G x y) : F = G := by
  have hinner (a : ℝ) : coleHopf m v (F a) y ≤ coleHopf m v (G a) y :=
    coleHopf_mono (HasLinearGrowth.of_lipschitz (hF.right a))
      (lipschitzWith_toNNReal_of_abs_sub_le (hF.right a)).continuous.measurable
      (HasLinearGrowth.of_lipschitz (hG.right a))
      (lipschitzWith_toNNReal_of_abs_sub_le (hG.right a)).continuous.measurable (hFG a) m v y
  have hall := coleHopf_eq_implies_eq_of_lipschitz
    (independentPairColeHopf_inner_lipschitz hF m v y)
    (independentPairColeHopf_inner_lipschitz hG m v y) hinner hm hv x he
  funext a
  exact coleHopf_eq_implies_eq_of_lipschitz (hF.right a) (hG.right a) (hFG a) hm hv y (congrFun hall a)

theorem independentPairColeHopf_lt_of_exists_lt {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) (hFG : ∀ x y, F x y ≤ G x y)
    (hstrict : ∃ x y, F x y < G x y) {m : ℝ} (hm : 0 ≤ m) {v : ℝ≥0} (hv : v ≠ 0) (x y : ℝ) :
    independentPairColeHopf m v F x y < independentPairColeHopf m v G x y := by
  apply lt_of_le_of_ne (independentPairColeHopf_mono hF hG hFG m v x y)
  intro he
  have hall := independentPairColeHopf_eq_implies_eq hF hG hFG hm hv x y he
  obtain ⟨a, b, hab⟩ := hstrict
  exact hab.ne (congrFun (congrFun hall a) b)

theorem correlatedPairColeHopf_eq_implies_diagonal_eq {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) (hFG : ∀ x y, F x y ≤ G x y)
    {η : ℝ} (hη : |η| = 1) {m : ℝ} (hm : 0 ≤ m) {v : ℝ≥0} (hv : v ≠ 0) (x y : ℝ)
    (he : correlatedPairColeHopf η m v F x y = correlatedPairColeHopf η m v G x y) :
    ∀ z, F (x + z) (y + η * z) = G (x + z) (y + η * z) := by
  have hall := coleHopf_eq_implies_eq_of_lipschitz (hF.signed_diagonal hη x y)
    (hG.signed_diagonal hη x y) (fun _z => hFG _ _) hm hv 0 he
  exact congrFun hall

theorem correlatedPairColeHopf_lt_of_exists_diagonal_lt {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) (hFG : ∀ x y, F x y ≤ G x y)
    {η : ℝ} (hη : |η| = 1) {m : ℝ} (hm : 0 ≤ m) {v : ℝ≥0} (hv : v ≠ 0) (x y : ℝ)
    (hstrict : ∃ z, F (x + z) (y + η * z) < G (x + z) (y + η * z)) :
    correlatedPairColeHopf η m v F x y < correlatedPairColeHopf η m v G x y :=
  coleHopf_lt_of_exists_lt (hF.signed_diagonal hη x y) (hG.signed_diagonal hη x y)
    (fun _z => hFG _ _) hstrict hm hv 0

end SpinGlass
