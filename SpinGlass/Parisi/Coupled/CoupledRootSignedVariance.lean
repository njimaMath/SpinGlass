import SpinGlass.Parisi.Coupled.CoupledRootSignedTransport

/-!
# Signed initial-interval covariance and correction witnesses

The driven profile uses the inserted overlap absolute value and sign minus
one. The auxiliary root remains common. Evenness supplies the negative
tangents and the unchanged theta correction under the original contract.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

noncomputable def parisiRootSignedCouplingRho {k : ℕ} (qs : Fin (k + 1) → ℝ) (u : ℝ) :
    Fin 2 → Fin 2 → ℕ → ℝ :=
  couplingRhoSgn (qExt (splitParisiRootOverlap qs |u|)) (-1) 1

/-- Evenness extends the proved positive-domain tangents to the
negative profile domain without new regularity assumptions. -/
theorem TalagrandXiCondition.tangent_line_le_signed {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {q : ℝ} (hq : q ∈ Icc (-1 : ℝ) 1) (x : ℝ) :
    ξ q + (x - q) * deriv ξ q ≤ ξ x := by
  rcases le_total 0 q with hq0 | hq0
  · exact hξ.tangent_line_le ⟨hq0, hq.2⟩ x
  · have hh := hξ.tangent_line_le (q := -q) ⟨by linarith, by linarith [hq.1]⟩ (-x)
    rw [hξ.even q, hξ.even x, deriv_neg_of_even hξ.even] at hh
    nlinarith

theorem parisiTimeProfile_tangent_line_le_signed {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {t : ℝ} (ht : 0 ≤ t) {q : ℝ} (hq : q ∈ Icc (-1 : ℝ) 1) (x : ℝ) :
    parisiTimeProfile ξ t q + (x - q) * deriv (parisiTimeProfile ξ t) q ≤
      parisiTimeProfile ξ t x := by
  have hh := mul_le_mul_of_nonneg_left (hξ.tangent_line_le_signed hq x) ht
  rw [deriv_parisiTimeProfile]
  dsimp only [parisiTimeProfile]
  nlinarith

theorem parisiRootSignedCouplingRho_zero {k : ℕ} (qs : Fin (k + 1) → ℝ) (u : ℝ) (l l' : Fin 2) :
    parisiRootSignedCouplingRho qs u l l' 0 = 0 :=
  couplingRhoSgn_zero _ (qExt_zero _) (-1) 1 l l'

theorem parisiRootSignedCouplingRho_mem_Icc {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (hq : ParisiQAdmissible qs) {u : ℝ} (hu : |u| ≤ qs 0) (l l' : Fin 2) (r : ℕ) :
    parisiRootSignedCouplingRho qs u l l' r ∈ Icc (-1 : ℝ) 1 := by
  obtain ⟨hmono, hzero, hone⟩ := mem_parisiOverlapDomain_iff.1
    (parisiRootOverlap_mem_domain_of_admissible qs hq ⟨abs_nonneg _, hu⟩)
  unfold parisiRootSignedCouplingRho couplingRhoSgn
  split_ifs
  · have hmem := qExt_mem_Icc hmono hzero hone r
    exact ⟨by linarith [hmem.1], hmem.2⟩
  · have hmem := qExt_mem_Icc hmono hzero hone (min r 1)
    rw [neg_one_mul]
    constructor <;> linarith [hmem.1, hmem.2]

/-- The actual driven root realizes the signed derivative increment. -/
theorem parisiRootSignedDrivenRootVar_mul_gram {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : 0 ≤ t) (hu : |u| ≤ qs 0) (l l' : Fin 2) :
    (parisiRootDrivenRootVar ξ qs t |u| : ℝ) * gram (couplingFactorSgn (-1) 1 0) l l' =
      deriv (parisiTimeProfile ξ t) (parisiRootSignedCouplingRho qs u l l' 1) -
        deriv (parisiTimeProfile ξ t) (parisiRootSignedCouplingRho qs u l l' 0) := by
  have he : parisiRootDrivenRootVar ξ qs t |u| =
      couplingVar (parisiTimeProfile ξ t) (qExt (splitParisiRootOverlap qs |u|)) 0 := by
    change t.toNNReal * parisiVar ξ (splitParisiRootOverlap qs |u|) 0 =
      parisiVar (parisiTimeProfile ξ t) (splitParisiRootOverlap qs |u|) 0
    exact (parisiVar_timeProfile ξ _ ht 0).symm
  have heven : Function.Even (parisiTimeProfile ξ t) := fun x => by
    simp only [parisiTimeProfile, hξ.even x]
  rw [he]
  unfold parisiRootSignedCouplingRho
  have hh := couplingVar_mul_gram (J'' := Fin 2) (τ := 1)
    (by norm_num : (-1 : ℝ) ^ 2 = 1)
    (deriv_sgn_mul_of_even heven (Or.inr rfl))
    (parisiTimeProfile_deriv_qExt_le_succ hξ
      (parisiRootOverlap_mem_domain_of_admissible qs hq ⟨abs_nonneg _, hu⟩) ht 0) l l'
  simpa only [gram_sumL, zero_add] using hh

/-- Every positive-level driven increment realizes the signed rho
array, including the inserted and terminal levels. -/
theorem parisiRootSignedDrivenVars_mul_gram {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : 0 ≤ t) (hu : |u| ≤ qs 0) (i : Fin (k + 2)) (l l' : Fin 2) :
    (parisiRootDrivenVars ξ qs t |u| i : ℝ) * gram (couplingFactorSgn (-1) 1 (i.val + 1)) l l' =
      deriv (parisiTimeProfile ξ t) (parisiRootSignedCouplingRho qs u l l' (i.val + 2)) -
        deriv (parisiTimeProfile ξ t) (parisiRootSignedCouplingRho qs u l l' (i.val + 1)) := by
  have he : parisiRootDrivenVars ξ qs t |u| i =
      couplingVar (parisiTimeProfile ξ t) (qExt (splitParisiRootOverlap qs |u|)) (i.val + 1) := by
    change t.toNNReal * parisiVar ξ (splitParisiRootOverlap qs |u|) (i.val + 1) =
      parisiVar (parisiTimeProfile ξ t) (splitParisiRootOverlap qs |u|) (i.val + 1)
    exact (parisiVar_timeProfile ξ _ ht _).symm
  have heven : Function.Even (parisiTimeProfile ξ t) := fun x => by
    simp only [parisiTimeProfile, hξ.even x]
  rw [he]
  unfold parisiRootSignedCouplingRho
  have hh := couplingVar_mul_gram (J'' := Fin 2) (τ := 1)
    (by norm_num : (-1 : ℝ) ^ 2 = 1)
    (deriv_sgn_mul_of_even heven (Or.inr rfl))
    (parisiTimeProfile_deriv_qExt_le_succ hξ
      (parisiRootOverlap_mem_domain_of_admissible qs hq ⟨abs_nonneg _, hu⟩) ht (i.val + 1)) l l'
  simpa only [gram_sumL, show i.val + 1 + 1 = i.val + 2 by omega] using hh

theorem parisiRootSignedCouplingRho_top {k : ℕ} (qs : Fin (k + 1) → ℝ) (u : ℝ) (l l' : Fin 2) :
    parisiRootSignedCouplingRho qs u l l' (k + 3) = if l = l' then 1 else -|u| := by
  have hh := couplingRhoSgn_top (qExt (splitParisiRootOverlap qs |u|)) (-1)
    (τ := 1) (κ := k + 2) (by omega) (qExt_of_le _ (by omega)) l l'
  unfold parisiRootSignedCouplingRho
  have hfirst : qExt (splitParisiRootOverlap qs |u|) 1 = |u| := by
    rw [qExt_succ_of_lt _ (by omega : 0 < k + 2)]
    rfl
  simpa only [neg_one_mul, hfirst, show k + 2 + 1 = k + 3 by omega] using hh

theorem pairDiagDefect_parisiRootSignedCouplingRho_top (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) {u : ℝ} (hu : u ≤ 0) :
    pairDiagDefect ξ u (fun l l' => parisiRootSignedCouplingRho qs u l l' (k + 3)) = 0 := by
  have he : (fun l l' => parisiRootSignedCouplingRho qs u l l' (k + 3)) =
      fun l l' => if l = l' then (1 : ℝ) else u := by
    funext l l'
    rw [parisiRootSignedCouplingRho_top, abs_of_nonpos hu, neg_neg]
  rw [he, pairDiagDefect_diag]

/-- Evenness leaves the exact root correction unchanged except for
the absolute value of the inserted overlap. -/
theorem coupledLevelSum_parisiRootSigned_eq_correction {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u m : ℝ) :
    (1 / 2) * coupledLevelSum (parisiTimeProfile ξ t) (parisiRootSignedCouplingRho qs u)
      (parisiRootResponseMasses ms m) =
      t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ |u|)) := by
  have heven : Function.Even (parisiTimeProfile ξ t) := fun x => by
    simp only [parisiTimeProfile, hξ.even x]
  have he : coupledLevelSum (parisiTimeProfile ξ t) (parisiRootSignedCouplingRho qs u)
      (parisiRootResponseMasses ms m) =
      coupledLevelSum (parisiTimeProfile ξ t) (parisiRootCouplingRho qs |u|)
        (parisiRootResponseMasses ms m) := by
    unfold parisiRootSignedCouplingRho parisiRootCouplingRho
    rw [coupledLevelSum_couplingRhoSgn (parisiTheta_sgn_mul_of_even heven (Or.inr rfl)),
      coupledLevelSum_couplingRhoSgn (fun x => by simp only [one_mul])]
  rw [he, coupledLevelSum_parisiRoot_eq_correction]

end SpinGlass
