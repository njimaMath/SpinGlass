import SpinGlass.Parisi.Coupled.CoupledRootMassLimit

/-!
# Independent branches at two arbitrary effective fields

The signed root construction has two different effective root fields.
The positive-mass branches are independent. Their zero-coupling value
factorizes, and the conditional slope is the product of the two actual
Cole-Hopf gradients.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable def independentPairSiteF {n : ℕ} (lam : ℝ) (x : Fin 2 → ℝ)
    (ys : Fin n → Fin 2 → ℝ) : ℝ :=
  pairSiteF lam x 0 (fun _ l j => if l = j then 1 else 0) 0 ys

noncomputable def independentPairSiteRec {n : ℕ} (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0)
    (lam : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  parisiRec n ms (siteGaussianMarks (Fin 2) n vs) (independentPairSiteF lam x)

theorem pairSiteMark_independent {n : ℕ} (ys : Fin n → Fin 2 → ℝ) (l : Fin 2) :
    pairSiteMark (0 : Fin 2 → Fin 2 → ℝ) (fun _ : Fin n => fun l j => if l = j then 1 else 0)
      0 ys l = ∑ p, ys p l := by
  simp [pairSiteMark, Finset.sum_ite_eq]

theorem independentPairSiteF_zero {n : ℕ} (x : Fin 2 → ℝ) (ys : Fin n → Fin 2 → ℝ) :
    independentPairSiteF 0 x ys = Real.log (Real.cosh (x 0 + ∑ p, ys p 0)) +
      Real.log (Real.cosh (x 1 + ∑ p, ys p 1)) := by
  unfold independentPairSiteF pairSiteF
  rw [pairSiteY_zero, pairSiteMark_independent, pairSiteMark_independent]

private noncomputable def independentPairWeight {n : ℕ} (x : Fin 2 → ℝ)
    (zs : Fin n → ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (Real.log (Real.cosh (x 0 + ∑ p, (zs p).1)))) *
    ENNReal.ofReal (Real.exp (Real.log (Real.cosh (x 1 + ∑ p, (zs p).2))))

private theorem measurable_independentPairWeight {n : ℕ} (x : Fin 2 → ℝ) :
    Measurable (independentPairWeight (n := n) x) := by
  unfold independentPairWeight
  fun_prop

private theorem independentPairWeight_map {n : ℕ} (x : Fin 2 → ℝ)
    (ys : Fin n → Fin 2 → ℝ) :
    independentPairWeight x (fun p => MeasurableEquiv.finTwoArrow (ys p)) =
      ENNReal.ofReal (Real.exp (independentPairSiteF 0 x ys)) := by
  rw [independentPairSiteF_zero, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rfl

/-- The actual conditional paired recursion at zero coupling is the
sum of the scalar recursions at its two effective fields. -/
theorem independentPairSiteRec_zero {n : ℕ} (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (x : Fin 2 → ℝ) :
    independentPairSiteRec ms vs 0 x = logCoshRec n ms vs (x 0) + logCoshRec n ms vs (x 1) := by
  let G := fun l : Fin 2 => fun zs : Fin n → ℝ =>
    ENNReal.ofReal (Real.exp (Real.log (Real.cosh (x l + ∑ p, zs p))))
  have hG (l : Fin 2) : Measurable (G l) := measurable_ofReal_exp_log_cosh_add_sum n (x l)
  have hpoint : (fun ys : Fin n → Fin 2 → ℝ => ENNReal.ofReal (Real.exp (independentPairSiteF 0 x ys))) =
      fun ys => independentPairWeight x (fun p => MeasurableEquiv.finTwoArrow (ys p)) := by
    funext ys
    exact (independentPairWeight_map x ys).symm
  have hmap : (fun p => (siteGaussianMarks (Fin 2) n vs p).map MeasurableEquiv.finTwoArrow) =
      fun p => (gaussianReal 0 (vs p)).prod (gaussianReal 0 (vs p)) := by
    funext p
    exact (measurePreserving_finTwoArrow (gaussianReal 0 (vs p))).map_eq
  have hRpos (l : Fin 2) : 0 < (cascadeRec n ms (fun p => gaussianReal 0 (vs p)) (G l)).toReal :=
    ENNReal.toReal_pos (cascadeRec_pos n ms _ (hG l)
      (fun zs => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos).ne'
      (cascadeRec_cosh_ne_top n ms vs hpos hle (x l))
  unfold independentPairSiteRec parisiRec
  rw [hpoint, ← cascadeRec_map n ms _ (fun _ => MeasurableEquiv.finTwoArrow)
    (fun _ => MeasurableEquiv.finTwoArrow.measurable) (measurable_independentPairWeight x), hmap]
  change Real.log (cascadeRec n ms (fun p => (gaussianReal 0 (vs p)).prod (gaussianReal 0 (vs p)))
    (fun zs => G 0 (fun p => (zs p).1) * G 1 (fun p => (zs p).2))).toReal = _
  rw [cascadeRec_prod n ms _ (hG 0) (hG 1) hpos, ENNReal.toReal_mul,
    Real.log_mul (hRpos 0).ne' (hRpos 1).ne']
  rfl

/-- Factorization of the shifted nonnegative magnetizations under
the actual paired tilted law at two different effective fields. -/
theorem cascadeTilt_independentPair_shift {n : ℕ} (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (x : Fin 2 → ℝ)
    (c : ℝ) (hc : 1 ≤ c) :
    cascadeTilt n ms (siteGaussianMarks (Fin 2) n vs)
      (fun ys => ENNReal.ofReal (Real.exp (independentPairSiteF 0 x ys)))
      (fun ys => ENNReal.ofReal ((Real.tanh (x 0 + ∑ p, ys p 0) + c) *
        (Real.tanh (x 1 + ∑ p, ys p 1) + c))) =
      ENNReal.ofReal ((deriv (coleHopfIterate n ms vs (parisiLogCoshTerminal 0)) (x 0) + c) *
        (deriv (coleHopfIterate n ms vs (parisiLogCoshTerminal 0)) (x 1) + c)) := by
  let G := fun l : Fin 2 => fun zs : Fin n → ℝ =>
    ENNReal.ofReal (Real.exp (Real.log (Real.cosh (x l + ∑ p, zs p))))
  let U := fun l : Fin 2 => fun zs : Fin n → ℝ =>
    ENNReal.ofReal (Real.tanh (x l + ∑ p, zs p) + c)
  let W := fun zs : Fin n → ℝ × ℝ => U 0 (fun p => (zs p).1) * U 1 (fun p => (zs p).2)
  have hG (l : Fin 2) : Measurable (G l) := measurable_ofReal_exp_log_cosh_add_sum n (x l)
  have hU (l : Fin 2) : Measurable (U l) := by
    dsimp only [U]
    fun_prop
  have hW : Measurable W := by dsimp only [W]; fun_prop
  have hweight : (fun ys : Fin n → Fin 2 → ℝ => ENNReal.ofReal (Real.exp (independentPairSiteF 0 x ys))) =
      fun ys => independentPairWeight x (fun p => MeasurableEquiv.finTwoArrow (ys p)) := by
    funext ys
    exact (independentPairWeight_map x ys).symm
  have hobs : (fun ys : Fin n → Fin 2 → ℝ => ENNReal.ofReal
      ((Real.tanh (x 0 + ∑ p, ys p 0) + c) * (Real.tanh (x 1 + ∑ p, ys p 1) + c))) =
      fun ys => W (fun p => MeasurableEquiv.finTwoArrow (ys p)) := by
    funext ys
    rw [ENNReal.ofReal_mul (by linarith [Real.neg_one_lt_tanh (x 0 + ∑ p, ys p 0)])]
    rfl
  have ht := cascadeTilt_coordinateMap n ms (siteGaussianMarks (Fin 2) n vs)
    (fun _ => MeasurableEquiv.finTwoArrow) (fun _ => MeasurableEquiv.finTwoArrow.measurable)
    (measurable_independentPairWeight x) hW
  have hmap : coordinateMapLaw (siteGaussianMarks (Fin 2) n vs)
      (fun _ => MeasurableEquiv.finTwoArrow) (fun _ => MeasurableEquiv.finTwoArrow.measurable) =
      fun p => (gaussianReal 0 (vs p)).prod (gaussianReal 0 (vs p)) := by
    funext p
    exact (measurePreserving_finTwoArrow (gaussianReal 0 (vs p))).map_eq
  have ht' : cascadeTilt n ms (fun p => (gaussianReal 0 (vs p)).prod (gaussianReal 0 (vs p)))
      (independentPairWeight x) W =
      cascadeTilt n ms (siteGaussianMarks (Fin 2) n vs)
        (fun zs => independentPairWeight x (fun i => MeasurableEquiv.finTwoArrow (zs i)))
        (fun zs => W (fun i => MeasurableEquiv.finTwoArrow (zs i))) := by
    simpa only [hmap] using ht
  rw [hweight, hobs, ← ht']
  change cascadeTilt n ms (fun p => (gaussianReal 0 (vs p)).prod (gaussianReal 0 (vs p)))
    (fun zs => G 0 (fun p => (zs p).1) * G 1 (fun p => (zs p).2)) W = _
  rw [← cascadeTiltProd_eq_cascadeTilt n ms _ (hG 0) (hG 1) hW
    (fun zs => ENNReal.ofReal_pos.2 (Real.exp_pos _))
    (fun zs => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos]
  change cascadeTiltProd n ms (fun p => gaussianReal 0 (vs p)) (G 0) (G 1)
    (fun zs => U 0 (fun p => (zs p).1) * U 1 (fun p => (zs p).2)) = _
  rw [cascadeTiltProd_prod n ms _ (hG 0) (hG 1) (hU 0) (hU 1)]
  have hshift (l : Fin 2) : cascadeTilt n ms (fun p => gaussianReal 0 (vs p)) (G l) (U l) =
      ENNReal.ofReal (deriv (coleHopfIterate n ms vs (parisiLogCoshTerminal 0)) (x l) + c) := by
    simpa only [G, U, parisiLogCoshTerminal, zero_add] using
      cascadeTilt_shiftedTanh_eq ms vs hpos hle (x l) c hc
  rw [hshift 0, hshift 1, ← ENNReal.ofReal_mul]
  have hL : ∀ y z, |parisiLogCoshTerminal 0 z - parisiLogCoshTerminal 0 y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0
  have hD : |deriv (coleHopfIterate n ms vs (parisiLogCoshTerminal 0)) (x 0)| ≤ 1 := by
    simpa only [Real.norm_eq_abs, Real.toNNReal_one, NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := x 0) (lipschitzWith_toNNReal_of_abs_sub_le
        (abs_coleHopfIterate_sub_le n ms vs (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0)) hL))
  linarith [(abs_le.1 hD).1]

/-- The signed conditional magnetization product is the product of
the two actual scalar gradients, under the paired tilted probability law. -/
theorem integral_independentPair_tanh_product {n : ℕ} (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (x : Fin 2 → ℝ) :
    (∫ ys, Real.tanh (x 0 + ∑ p, ys p 0) * Real.tanh (x 1 + ∑ p, ys p 1)
      ∂cascadeTiltMeasure n ms (siteGaussianMarks (Fin 2) n vs)
        (fun ys => ENNReal.ofReal (Real.exp (independentPairSiteF 0 x ys)))) =
      deriv (coleHopfIterate n ms vs (parisiLogCoshTerminal 0)) (x 0) *
        deriv (coleHopfIterate n ms vs (parisiLogCoshTerminal 0)) (x 1) := by
  let μ := cascadeTiltMeasure n ms (siteGaussianMarks (Fin 2) n vs)
    (fun ys => ENNReal.ofReal (Real.exp (independentPairSiteF 0 x ys)))
  let T := fun l : Fin 2 => fun ys : Fin n → Fin 2 → ℝ => Real.tanh (x l + ∑ p, ys p l)
  let D := deriv (coleHopfIterate n ms vs (parisiLogCoshTerminal 0))
  let S := fun c : ℝ => fun ys : Fin n → Fin 2 → ℝ => (T 0 ys + c) * (T 1 ys + c)
  have : IsProbabilityMeasure μ := isProbabilityMeasure_cascadeTiltMeasure_pairSiteF
    ms hpos hle vs 0 x 0 (fun _ l j => if l = j then 1 else 0) 0
  have hT (l : Fin 2) : Measurable (T l) := by dsimp only [T]; fun_prop
  have hTb (l : Fin 2) (ys : Fin n → Fin 2 → ℝ) : |T l ys| ≤ 1 := (Real.abs_tanh_lt_one _).le
  have hL : ∀ y z, |parisiLogCoshTerminal 0 z - parisiLogCoshTerminal 0 y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0
  have hD (l : Fin 2) : |D (x l)| ≤ 1 := by
    simpa only [Real.norm_eq_abs, Real.toNNReal_one, NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := x l) (lipschitzWith_toNNReal_of_abs_sub_le
        (abs_coleHopfIterate_sub_le n ms vs (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0)) hL))
  have hSm (c : ℝ) : Measurable (S c) := (hT 0 |>.add_const c).mul (hT 1 |>.add_const c)
  have hSnonneg (c : ℝ) (hc : 1 ≤ c) (ys : Fin n → Fin 2 → ℝ) : 0 ≤ S c ys :=
    mul_nonneg (by linarith [(abs_le.1 (hTb 0 ys)).1]) (by linarith [(abs_le.1 (hTb 1 ys)).1])
  have hi (c : ℝ) (hc : 1 ≤ c) : Integrable (S c) μ := by
    apply Integrable.of_bound (hSm c).aestronglyMeasurable ((c + 1) ^ 2) (.of_forall fun ys => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hSnonneg c hc ys)]
    calc
      S c ys ≤ (c + 1) * (T 1 ys + c) :=
        mul_le_mul_of_nonneg_right (by linarith [(abs_le.1 (hTb 0 ys)).2])
          (by linarith [(abs_le.1 (hTb 1 ys)).1])
      _ ≤ (c + 1) * (c + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 (hTb 1 ys)).2]) (by linarith)
      _ = (c + 1) ^ 2 := by ring
  have hFm : Measurable (independentPairSiteF (n := n) 0 x) :=
    measurable_pairSiteF' 0 x 0 (fun _ l j => if l = j then 1 else 0) 0
  have hGm := hFm.exp.ennreal_ofReal
  have hshift (c : ℝ) (hc : 1 ≤ c) : (∫ ys, S c ys ∂μ) = (D (x 0) + c) * (D (x 1) + c) := by
    rw [integral_eq_lintegral_of_nonneg_ae (.of_forall (hSnonneg c hc)) (hSm c).aestronglyMeasurable]
    unfold μ
    rw [lintegral_cascadeTiltMeasure n ms _ hGm (hSm c).ennreal_ofReal]
    change (cascadeTilt n ms (siteGaussianMarks (Fin 2) n vs)
      (fun ys => ENNReal.ofReal (Real.exp (independentPairSiteF 0 x ys)))
      (fun ys => ENNReal.ofReal ((Real.tanh (x 0 + ∑ p, ys p 0) + c) *
        (Real.tanh (x 1 + ∑ p, ys p 1) + c)))).toReal = _
    rw [cascadeTilt_independentPair_shift ms vs hpos hle x c hc,
      ENNReal.toReal_ofReal (mul_nonneg (by linarith [(abs_le.1 (hD 0)).1])
        (by linarith [(abs_le.1 (hD 1)).1]))]
  change (∫ ys, T 0 ys * T 1 ys ∂μ) = D (x 0) * D (x 1)
  calc
    _ = ∫ ys, 2 * S 1 ys - S 2 ys + 2 ∂μ := integral_congr_ae (.of_forall fun ys => by dsimp only [S]; ring)
    _ = 2 * (∫ ys, S 1 ys ∂μ) - (∫ ys, S 2 ys ∂μ) + 2 := by
      have ha := integral_add ((hi 1 le_rfl).const_mul 2 |>.sub (hi 2 (by norm_num))) (integrable_const 2)
      have hs := integral_sub ((hi 1 le_rfl).const_mul 2) (hi 2 (by norm_num))
      simp only [Pi.sub_apply] at ha hs
      rw [ha, hs, integral_const_mul,
        integral_const, probReal_univ, one_smul]
    _ = _ := by rw [hshift 1 le_rfl, hshift 2 (by norm_num)]; ring

/-- The actual two-field conditional coupling slope is the product
of the scalar Cole-Hopf gradients. The fields may have either sign. -/
theorem hasDerivAt_independentPairSiteRec_zero {n : ℕ} (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (x : Fin 2 → ℝ) :
    HasDerivAt (fun lam => independentPairSiteRec ms vs lam x)
      (deriv (coleHopfIterate n ms vs (parisiLogCoshTerminal 0)) (x 0) *
        deriv (coleHopfIterate n ms vs (parisiLogCoshTerminal 0)) (x 1)) 0 := by
  have hd := hasDerivAt_parisiRec_pairSiteF ms hpos hle vs 0 x 0
    (fun _ l j => if l = j then 1 else 0) 0
  simp_rw [pairSiteF'_zero, pairSiteMark_independent] at hd
  change HasDerivAt (fun lam => independentPairSiteRec ms vs lam x)
    (∫ ys, Real.tanh (x 0 + ∑ p, ys p 0) * Real.tanh (x 1 + ∑ p, ys p 1)
      ∂cascadeTiltMeasure n ms (siteGaussianMarks (Fin 2) n vs)
        (fun ys => ENNReal.ofReal (Real.exp (independentPairSiteF 0 x ys)))) 0 at hd
  rw [integral_independentPair_tanh_product ms vs hpos hle x] at hd
  exact hd

/-- The two-field conditional Taylor estimate has the actual product
gradient as its linear term and the uniform quadratic coefficient one half. -/
theorem independentPairSiteRec_le_taylor {n : ℕ} (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0)
    (hmono : Monotone ms) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (x : Fin 2 → ℝ) (lam : ℝ) :
    independentPairSiteRec ms vs lam x ≤ logCoshRec n ms vs (x 0) + logCoshRec n ms vs (x 1) +
      (deriv (coleHopfIterate n ms vs (parisiLogCoshTerminal 0)) (x 0) *
        deriv (coleHopfIterate n ms vs (parisiLogCoshTerminal 0)) (x 1)) * lam + lam ^ 2 / 2 := by
  have hY (l : ℝ) : pairSiteY₀ ms 0 vs l x (0 : Fin 2 → Fin 2 → ℝ)
      (fun _ l j => if l = j then 1 else 0) = independentPairSiteRec ms vs l x := by
    unfold pairSiteY₀
    rw [pi_gaussianReal_zero_eq_dirac, integral_dirac]
    rfl
  have he : (fun l => pairSiteY₀ ms 0 vs l x (0 : Fin 2 → Fin 2 → ℝ)
      (fun _ l j => if l = j then 1 else 0)) = fun l => independentPairSiteRec ms vs l x := funext hY
  have hd := hasDerivAt_pairSiteY₀ ms hpos hle 0 vs 0 x (0 : Fin 2 → Fin 2 → ℝ)
    (fun _ l j => if l = j then 1 else 0)
  rw [he] at hd
  have hgrad := hd.unique (hasDerivAt_independentPairSiteRec_zero ms vs hpos hle x)
  have hb := pairSiteY₀_le_taylor ms 0 vs lam x (0 : Fin 2 → Fin 2 → ℝ)
    (fun _ l j => if l = j then 1 else 0) hmono hpos hle
  rw [hY lam, hY 0, hgrad, independentPairSiteRec_zero ms vs hpos hle x] at hb
  exact hb

/-- The positive inserted root branch has the two scalar root layers
as its actual zero-coupling value at arbitrary effective root fields. -/
theorem independentPairSiteRec_parisi_root_zero (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (v : ℝ) (x : Fin 2 → ℝ) :
    independentPairSiteRec (parisiRootResponseMasses ms m) (parisiRootResponseVars ξ qs v) 0 x =
      coleHopf m v.toNNReal (parisiRootSuffix ξ ms qs) (x 0) +
        coleHopf m v.toNNReal (parisiRootSuffix ξ ms qs) (x 1) := by
  have hpos := parisiRootResponseMasses_pos ms hm hm0
  rw [independentPairSiteRec_zero _ _ hpos (parisiRootResponseMasses_le_one ms hm hm1)]
  simp_rw [logCoshRec_eq_coleHopfIterate_terminal_zero _ _ hpos]
  simp only [parisiRootResponseMasses, parisiRootResponseVars, coleHopfIterate_succ,
    Fin.cons_zero, Fin.tail_cons, parisiRootSuffix]

/-- The root branch conditional slope is the product of the two
positive inserted-layer gradients, before averaging their joint root law. -/
theorem hasDerivAt_independentPairSiteRec_parisi_root_zero (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (v : ℝ) (x : Fin 2 → ℝ) :
    HasDerivAt (fun lam => independentPairSiteRec (parisiRootResponseMasses ms m)
      (parisiRootResponseVars ξ qs v) lam x)
      (deriv (coleHopf m v.toNNReal (parisiRootSuffix ξ ms qs)) (x 0) *
        deriv (coleHopf m v.toNNReal (parisiRootSuffix ξ ms qs)) (x 1)) 0 := by
  have hd := hasDerivAt_independentPairSiteRec_zero (parisiRootResponseMasses ms m)
    (parisiRootResponseVars ξ qs v) (parisiRootResponseMasses_pos ms hm hm0)
    (parisiRootResponseMasses_le_one ms hm hm1) x
  simpa only [parisiRootResponseMasses, parisiRootResponseVars, coleHopfIterate_succ,
    Fin.cons_zero, Fin.tail_cons, parisiRootSuffix] using hd

/-- The gradient product has an actual zero-mass limit under every
probability law of two measurable root fields, with the constant envelope one. -/
theorem continuousAt_integral_pair_deriv_coleHopf_mass_zero {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → Fin 2 → ℝ} (hH : Measurable H) {A : ℝ → ℝ} (hA : ContDiff ℝ 2 A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|) {C : ℝ}
    (hsecond : ∀ y, |deriv (deriv A) y| ≤ C) (v : ℝ≥0) :
    ContinuousAt (fun m => ∫ ω, deriv (coleHopf m v A) (H ω 0) *
      deriv (coleHopf m v A) (H ω 1) ∂μ) 0 := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hLip
  have hfirst : ∀ y, |deriv A y| ≤ 1 := by
    intro y
    simpa only [Real.norm_eq_abs, Real.toNNReal_one, NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := y) (lipschitzWith_toNNReal_of_abs_sub_le hL)
  have hB : ∀ m y, |deriv (coleHopf m v A) y| ≤ 1 := by
    intro m y
    simpa only [Real.norm_eq_abs, Real.toNNReal_one, NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := y) (lipschitzWith_toNNReal_of_abs_sub_le
        (abs_coleHopf_sub_le_of_lipschitz m hA.continuous.measurable hL v))
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · exact .of_forall fun m => (((measurable_deriv (coleHopf m v A)).comp
      ((measurable_pi_apply 0).comp hH)).mul ((measurable_deriv (coleHopf m v A)).comp
      ((measurable_pi_apply 1).comp hH))).aestronglyMeasurable
  · exact .of_forall fun m => .of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_mul]
      simpa only [one_mul] using mul_le_mul (hB m (H ω 0)) (hB m (H ω 1))
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · exact integrable_const 1
  · exact .of_forall fun ω =>
      (continuousAt_deriv_coleHopf_mass_zero hA hfirst hsecond v (H ω 0)).tendsto.mul
        (continuousAt_deriv_coleHopf_mass_zero hA hfirst hsecond v (H ω 1)).tendsto

end SpinGlass
