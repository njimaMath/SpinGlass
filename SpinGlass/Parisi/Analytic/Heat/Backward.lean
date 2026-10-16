import SpinGlass.Parisi.Analytic.Heat.Taylor

/-!
# Heat Backward analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle.Heat`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators ENNReal NNReal

namespace SpinGlass.Aristotle

noncomputable section

namespace Heat

theorem heat_sub_div {t : ℝ} {f g : ℝ → ℝ} (x c : ℝ)
    (hf : Integrable (fun z => f (x + z)) (gaussianReal 0 t.toNNReal))
    (hg : Integrable (fun z => g (x + z)) (gaussianReal 0 t.toNNReal)) :
    (heat t f x - heat t g x) / c = heat t (fun y => (f y - g y) / c) x := by
  simp only [heat]; rw [← integral_sub hf hg, integral_div]

/-- Mean-value bound in the time variable. -/
theorem abs_sub_le_of_time {h g : ℝ → ℝ → ℝ} {a C K : ℝ}
    (htime : ∀ y, ∀ w ∈ Icc 0 a, HasDerivWithinAt (fun u => h u y) (g w y) (Icc 0 a) w)
    (hbv : ∀ w ∈ Icc 0 a, ∀ y, |g w y| ≤ C * Real.exp (K * |y|)) {v w : ℝ}
    (hv : v ∈ Icc 0 a) (hw : w ∈ Icc 0 a) (y : ℝ) :
    |h w y - h v y| ≤ C * Real.exp (K * |y|) * |w - v| := by
  have := (convex_Icc 0 a).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u => h u y) (f' := fun u => g u y) (fun u hu => htime y u hu)
    (fun u hu => by rw [Real.norm_eq_abs]; exact hbv u hu y) hv hw
  simpa [Real.norm_eq_abs] using this

/-- Difference quotients in time converge along moving base points when the time derivative
is jointly continuous. -/
theorem tendsto_slope_joint {h g : ℝ → ℝ → ℝ} {a v y₀ : ℝ}
    (htime : ∀ y, ∀ w ∈ Icc 0 a, HasDerivWithinAt (fun u => h u y) (g w y) (Icc 0 a) w)
    (hcont : ContinuousWithinAt (fun p : ℝ × ℝ => g p.1 p.2) (Icc 0 a ×ˢ univ) (v, y₀))
    (hv : v ∈ Icc 0 a) {ι : Type*} {l : Filter ι} {w y : ι → ℝ}
    (hw : Tendsto w l (𝓝[Icc 0 a \ {v}] v)) (hy : Tendsto y l (𝓝 y₀)) :
    Tendsto (fun i => (h (w i) (y i) - h v (y i)) / (w i - v)) l (𝓝 (g v y₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.1 hcont (ε / 2) (half_pos hε)
  have hw1 : ∀ᶠ i in l, w i ∈ Icc 0 a \ {v} := hw (self_mem_nhdsWithin)
  have hw2 : ∀ᶠ i in l, dist (w i) v < δ :=
    (tendsto_nhdsWithin_iff.1 hw).1 (Metric.ball_mem_nhds v hδ)
  have hy2 : ∀ᶠ i in l, dist (y i) y₀ < δ := (Metric.tendsto_nhds.1 hy) δ hδ
  filter_upwards [hw1, hw2, hy2] with i hi1 hi2 hi3
  set c := g v y₀
  have hne : w i - v ≠ 0 := sub_ne_zero.2 hi1.2
  have hsub : uIcc v (w i) ⊆ Icc 0 a := uIcc_subset_Icc hv hi1.1
  have key := (convex_uIcc v (w i)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u => h u (y i) - u * c) (f' := fun u => g u (y i) - c) (C := ε / 2)
    (fun u hu => ((htime (y i) u (hsub hu)).mono hsub).sub
      ((hasDerivWithinAt_id u _).mul_const c) |>.congr_deriv (by simp))
    (fun u hu => by
      have hu' : (u, y i) ∈ Icc 0 a ×ˢ (univ : Set ℝ) := ⟨hsub hu, trivial⟩
      have hd : dist (u, y i) (v, y₀) < δ := by
        rw [Prod.dist_eq, max_lt_iff]
        refine ⟨?_, hi3⟩
        rw [Real.dist_eq] at hi2 ⊢
        exact lt_of_le_of_lt (by simpa using abs_sub_left_of_mem_uIcc hu) hi2
      have := hδε hu' hd
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]; exact this.le) left_mem_uIcc right_mem_uIcc
  rw [Real.dist_eq]
  simp only [Real.norm_eq_abs] at key
  have e : (h (w i) (y i) - h v (y i)) / (w i - v) - c =
      ((h (w i) (y i) - w i * c) - (h v (y i) - v * c)) / (w i - v) := by
    field_simp; ring
  rw [e, abs_div]
  rw [div_lt_iff₀ (abs_pos.2 hne)]
  calc _ ≤ ε / 2 * |w i - v| := key
    _ < ε * |w i - v| := by
        have := abs_pos.2 hne
        nlinarith

/-- The heat difference quotient `(heat δ f - f) / δ` converges to half of the second
derivative, uniformly along families. -/
theorem tendsto_heat_quotient {a : ℝ} {h h₁ h₂ h₃ : ℝ → ℝ → ℝ}
    (hd₁ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h w) (h₁ w y) y)
    (hd₂ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h₁ w) (h₂ w y) y)
    (hd₃ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h₂ w) (h₃ w y) y) {C K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ w ∈ Icc 0 a, ∀ y, |h w y| ≤ C * Real.exp (K * |y|))
    (hb₃ : ∀ w ∈ Icc 0 a, ∀ y, |h₃ w y| ≤ C * Real.exp (K * |y|))
    {ι : Type*} {l : Filter ι} {w δ y : ι → ℝ} {y₀ L : ℝ}
    (hw : ∀ᶠ i in l, w i ∈ Icc 0 a) (hδ : Tendsto δ l (𝓝[>] 0)) (hδa : ∀ᶠ i in l, δ i ≤ a)
    (hy : Tendsto y l (𝓝 y₀)) (h2lim : Tendsto (fun i => h₂ (w i) (y i)) l (𝓝 L)) :
    Tendsto (fun i => (heat (δ i) (h (w i)) (y i) - h (w i) (y i)) / δ i) l (𝓝 (L / 2)) := by
  have hδpos : ∀ᶠ i in l, 0 < δ i := hδ self_mem_nhdsWithin
  have hδ0 : Tendsto δ l (𝓝 0) := tendsto_nhdsWithin_iff.1 hδ |>.1
  set E := fun i => (heat (δ i) (h (w i)) (y i) - h (w i) (y i)) / δ i - h₂ (w i) (y i) / 2
  have hE : Tendsto E l (𝓝 0) := by
    have hbound : Tendsto (fun i => C * taylorConst K a * Real.sqrt (δ i) *
        Real.exp (K * |y i|)) l (𝓝 0) := by
      have : Tendsto (fun i => C * taylorConst K a * Real.sqrt (δ i) *
          Real.exp (K * |y i|)) l
          (𝓝 (C * taylorConst K a * Real.sqrt 0 * Real.exp (K * |y₀|))) :=
        ((tendsto_const_nhds.mul ((Real.continuous_sqrt.tendsto 0).comp hδ0)).mul
          ((Real.continuous_exp.tendsto _).comp
            ((continuous_abs.tendsto _).comp hy |>.const_mul K)))
      simpa using this
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hw, hδpos, hδa] with i hwi hδi hδai
    have := heat_short_time (hd₁ (w i) hwi) (hd₂ (w i) hwi) (hd₃ (w i) hwi) hK (hb (w i) hwi)
      (hb₃ (w i) hwi) hδi.le hδai (y i)
    rw [Real.norm_eq_abs]
    have e : E i = (heat (δ i) (h (w i)) (y i) - h (w i) (y i) - δ i / 2 * h₂ (w i) (y i)) /
        δ i := by simp only [E]; field_simp
    rw [e, abs_div, abs_of_pos hδi, div_le_iff₀ hδi]
    have hs : δ i * Real.sqrt (δ i) = Real.sqrt (δ i) * δ i := mul_comm _ _
    rw [hs] at this
    linarith
  have := hE.add (h2lim.div_const 2)
  simp only [zero_add] at this
  refine this.congr fun i => ?_
  simp only [E]; ring

/-- **Backward differentiation formula.** For a time-dependent integrand `h w` with
three space derivatives and a jointly continuous time derivative `hv'`,
`d/dw heat (a - w) (h w) x = heat (a - w) (∂_w h - h'' / 2) x` on `[0, a]`, including
both endpoints. -/
theorem hasDerivWithinAt_heat_backward {a x v : ℝ} (hv : v ∈ Icc 0 a)
    {h h₁ h₂ h₃ hv' : ℝ → ℝ → ℝ}
    (hd₁ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h w) (h₁ w y) y)
    (hd₂ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h₁ w) (h₂ w y) y)
    (hd₃ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h₂ w) (h₃ w y) y)
    (hb : UExp (Icc 0 a) h) (hb₂ : UExp (Icc 0 a) h₂) (hb₃ : UExp (Icc 0 a) h₃)
    (hbv : UExp (Icc 0 a) hv')
    (htime : ∀ y, ∀ w ∈ Icc 0 a, HasDerivWithinAt (fun u => h u y) (hv' w y) (Icc 0 a) w)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => hv' p.1 p.2) (Icc 0 a ×ˢ univ))
    (hcont₂ : ∀ y, ContinuousWithinAt (fun w => h₂ w y) (Icc 0 a) v) :
    HasDerivWithinAt (fun w => heat (a - w) (h w) x)
      (heat (a - v) (fun y => hv' v y - h₂ v y / 2) x) (Icc 0 a) v := by
  obtain ⟨C, K, hC, hK, hB⟩ := (((hb.abs.add hb₂.abs).add hb₃.abs).add hbv.abs).nonneg
  have b0 : ∀ w ∈ Icc 0 a, ∀ y, |h w y| ≤ C * Real.exp (K * |y|) := fun w hw y => by
    have := hB w hw y; rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (h₂ w y), abs_nonneg (h₃ w y), abs_nonneg (hv' w y)]
  have b2 : ∀ w ∈ Icc 0 a, ∀ y, |h₂ w y| ≤ C * Real.exp (K * |y|) := fun w hw y => by
    have := hB w hw y; rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (h w y), abs_nonneg (h₃ w y), abs_nonneg (hv' w y)]
  have b3 : ∀ w ∈ Icc 0 a, ∀ y, |h₃ w y| ≤ C * Real.exp (K * |y|) := fun w hw y => by
    have := hB w hw y; rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (h w y), abs_nonneg (h₂ w y), abs_nonneg (hv' w y)]
  have bv : ∀ w ∈ Icc 0 a, ∀ y, |hv' w y| ≤ C * Real.exp (K * |y|) := fun w hw y => by
    have := hB w hw y; rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (h w y), abs_nonneg (h₂ w y), abs_nonneg (h₃ w y)]
  have hcf : ∀ w ∈ Icc 0 a, Continuous (h w) := fun w hw =>
    continuous_iff_continuousAt.2 fun y => (hd₁ w hw y).continuousAt
  have hc2 : ∀ w ∈ Icc 0 a, Continuous (h₂ w) := fun w hw =>
    continuous_iff_continuousAt.2 fun y => (hd₃ w hw y).continuousAt
  have hcv : Continuous (hv' v) := by
    exact hcont.comp_continuous (by fun_prop : Continuous fun y : ℝ => (v, y))
      fun y => ⟨hv, trivial⟩
  set k : ℝ → ℝ := fun y => hv' v y - h₂ v y / 2
  have hk : Continuous k := hcv.sub ((hc2 v hv).div_const 2)
  have hkb : ∀ y, |k y| ≤ (3 / 2 * C) * Real.exp (K * |y|) := fun y => by
    have := abs_sub (hv' v y) (h₂ v y / 2)
    rw [abs_div, abs_two] at this
    have := bv v hv y; have := b2 v hv y
    simp only [k]; nlinarith
  set T := taylorConst K a
  have hT := taylorConst_nonneg K a
  -- bound on the Taylor quotient
  have tq_bound : ∀ w ∈ Icc 0 a, ∀ δ, 0 < δ → δ ≤ a → ∀ y,
      |(heat δ (h w) y - h w y) / δ| ≤ (C / 2 + C * T * Real.sqrt a) * Real.exp (K * |y|) := by
    intro w hw δ hδ hδa y
    have := heat_short_time (hd₁ w hw) (hd₂ w hw) (hd₃ w hw) hK (b0 w hw) (b3 w hw) hδ.le hδa y
    have h2 := b2 w hw y
    have e : (heat δ (h w) y - h w y) / δ =
        (heat δ (h w) y - h w y - δ / 2 * h₂ w y) / δ + h₂ w y / 2 := by field_simp; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_of_pos hδ, abs_div, abs_two]
    have hsq : Real.sqrt δ ≤ Real.sqrt a := Real.sqrt_le_sqrt hδa
    have hE := Real.exp_pos (K * |y|)
    have h1 : |heat δ (h w) y - h w y - δ / 2 * h₂ w y| / δ ≤
        C * T * Real.sqrt a * Real.exp (K * |y|) := by
      rw [div_le_iff₀ hδ]
      refine this.trans ?_
      have := mul_le_mul_of_nonneg_left hsq
        (by positivity : 0 ≤ C * T * Real.exp (K * |y|) * δ)
      calc C * T * (δ * Real.sqrt δ) * Real.exp (K * |y|)
          = C * T * Real.exp (K * |y|) * δ * Real.sqrt δ := by ring
        _ ≤ C * T * Real.exp (K * |y|) * δ * Real.sqrt a := this
        _ = _ := by ring
    have : (C / 2 + C * T * Real.sqrt a) * Real.exp (K * |y|) =
        C / 2 * Real.exp (K * |y|) + C * T * Real.sqrt a * Real.exp (K * |y|) := by ring
    rw [this]
    linarith
  -- bound on the slope quotient
  have sl_bound : ∀ w ∈ Icc 0 a, w ≠ v → ∀ y,
      |(h w y - h v y) / (w - v)| ≤ C * Real.exp (K * |y|) := by
    intro w hw hne y
    have := abs_sub_le_of_time htime bv hv hw y
    rw [abs_div, div_le_iff₀ (abs_pos.2 (sub_ne_zero.2 hne))]
    exact this
  have hsplit : Icc 0 a = Icc 0 v ∪ Icc v a := (Icc_union_Icc_eq_Icc hv.1 hv.2).symm
  rw [hsplit]
  refine HasDerivWithinAt.union ?_ ?_
  · -- left branch
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hsub : Icc 0 v \ {v} ⊆ Icc 0 a \ {v} :=
      sdiff_subset_sdiff_left (Icc_subset_Icc le_rfl hv.2)
    have hl : ∀ w ∈ Icc 0 v \ {v}, slope (fun w => heat (a - w) (h w) x) v w =
        ∫ z, (fun y => (h w y - h v y) / (w - v) - (heat (v - w) (h w) y - h w y) / (v - w))
          (x + Real.sqrt (a - v) * z) ∂(gaussianReal 0 1) := by
      intro w hw
      have hw' : w ∈ Icc 0 a := ⟨hw.1.1, hw.1.2.trans hv.2⟩
      have hwv : w < v := lt_of_le_of_ne hw.1.2 hw.2
      have hH := heat_heat (s := a - v) (t := v - w) (by linarith [hv.2]) (by linarith)
        (hcf w hw') (b0 w hw') x
      rw [show a - v + (v - w) = a - w by ring] at hH
      have hcg : Continuous (heat (v - w) (h w)) :=
        (continuous_heat (hcf w hw') (b0 w hw')).comp (Continuous.prodMk_right _)
      rw [slope_def_field, ← hH, heat_sub_div]
      · rw [heat_eq_std _ (by
          refine (hcg.sub (hcf v hv)).div_const _)]
        congr 1; funext z
        have : w - v ≠ 0 := sub_ne_zero.2 hwv.ne
        have : v - w ≠ 0 := sub_ne_zero.2 hwv.ne'
        field_simp; ring
      · exact integrable_shift hcg (fun y => abs_heat_le (hcf w hw') hK (b0 w hw') le_rfl y) x _
      · exact integrable_shift (hcf v hv) (b0 v hv) x _
    refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun w hw => (hl w hw).symm) ?_
    rw [heat_eq_std _ hk]
    have hmem : ∀ᶠ w in 𝓝[Icc 0 v \ {v}] v, w ∈ Icc 0 v \ {v} := self_mem_nhdsWithin
    refine tendsto_integral_std (x := fun _ => x) (s := fun _ => Real.sqrt (a - v))
      (q := fun w y => (h w y - h v y) / (w - v) - (heat (v - w) (h w) y - h w y) / (v - w))
      (k := k) tendsto_const_nhds tendsto_const_nhds ?_ ?_ fun z => ?_
    · filter_upwards [hmem] with w hw
      have hw' : w ∈ Icc 0 a := ⟨hw.1.1, hw.1.2.trans hv.2⟩
      exact (((hcf w hw').sub (hcf v hv)).div_const _ |>.sub
        ((((continuous_heat (hcf w hw') (b0 w hw')).comp (Continuous.prodMk_right _)).sub
          (hcf w hw')).div_const _)).comp (by fun_prop) |>.aestronglyMeasurable
    · refine ⟨C + (C / 2 + C * T * Real.sqrt a), K, ?_⟩
      filter_upwards [hmem] with w hw y
      have hw' : w ∈ Icc 0 a := ⟨hw.1.1, hw.1.2.trans hv.2⟩
      have hwv : w < v := lt_of_le_of_ne hw.1.2 hw.2
      refine (abs_sub _ _).trans ?_
      have := sl_bound w hw' hw.2 y
      have := tq_bound w hw' (v - w) (by linarith) (by linarith [hw.1.1, hv.2]) y
      linarith
    · have hA := tendsto_slope_joint (y := fun _ => x + Real.sqrt (a - v) * z) htime
        (hcont (v, _) ⟨hv, trivial⟩) hv (tendsto_nhdsWithin_mono_right hsub
          (tendsto_id (x := 𝓝[Icc 0 v \ {v}] v))) tendsto_const_nhds
      have hδ : Tendsto (fun w => v - w) (𝓝[Icc 0 v \ {v}] v) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have : Tendsto (fun w => v - w) (𝓝 v) (𝓝 (v - v)) :=
            tendsto_const_nhds.sub tendsto_id
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [hmem] with w hw
          exact sub_pos.2 (lt_of_le_of_ne hw.1.2 hw.2)
      have hB := tendsto_heat_quotient (w := fun w => w) (y := fun _ => x + Real.sqrt (a - v) * z)
        hd₁ hd₂ hd₃ hK b0 b3 (hmem.mono fun w hw => ⟨hw.1.1, hw.1.2.trans hv.2⟩) hδ
        (hmem.mono fun w hw => by linarith [hw.1.1, hv.2]) tendsto_const_nhds
        ((hcont₂ _).mono_left (nhdsWithin_mono _ (hsub.trans sdiff_subset)))
      exact hA.sub hB
  · -- right branch
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hsub : Icc v a \ {v} ⊆ Icc 0 a \ {v} :=
      sdiff_subset_sdiff_left (Icc_subset_Icc hv.1 le_rfl)
    have hr : ∀ w ∈ Icc v a \ {v}, slope (fun w => heat (a - w) (h w) x) v w =
        ∫ z, (fun y => (h w y - h v y) / (w - v) - (heat (w - v) (h v) y - h v y) / (w - v))
          (x + Real.sqrt (a - w) * z) ∂(gaussianReal 0 1) := by
      intro w hw
      have hw' : w ∈ Icc 0 a := ⟨hv.1.trans hw.1.1, hw.1.2⟩
      have hwv : v < w := lt_of_le_of_ne hw.1.1 (Ne.symm hw.2)
      have hH := heat_heat (s := a - w) (t := w - v) (by linarith [hw.1.2]) (by linarith)
        (hcf v hv) (b0 v hv) x
      rw [show a - w + (w - v) = a - v by ring] at hH
      have hcg : Continuous (heat (w - v) (h v)) :=
        (continuous_heat (hcf v hv) (b0 v hv)).comp (Continuous.prodMk_right _)
      rw [slope_def_field, ← hH, heat_sub_div]
      · rw [heat_eq_std _ (by
          refine ((hcf w hw').sub hcg).div_const _)]
        congr 1; funext z
        have : w - v ≠ 0 := sub_ne_zero.2 hwv.ne'
        field_simp; ring
      · exact integrable_shift (hcf w hw') (b0 w hw') x _
      · exact integrable_shift hcg (fun y => abs_heat_le (hcf v hv) hK (b0 v hv) le_rfl y) x _
    refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun w hw => (hr w hw).symm) ?_
    rw [heat_eq_std _ hk]
    have hmem : ∀ᶠ w in 𝓝[Icc v a \ {v}] v, w ∈ Icc v a \ {v} := self_mem_nhdsWithin
    have hsq : Tendsto (fun w => Real.sqrt (a - w)) (𝓝[Icc v a \ {v}] v)
        (𝓝 (Real.sqrt (a - v))) :=
      ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).tendsto v).mono_left
        nhdsWithin_le_nhds
    refine tendsto_integral_std (x := fun _ => x) (s := fun w => Real.sqrt (a - w))
      (q := fun w y => (h w y - h v y) / (w - v) - (heat (w - v) (h v) y - h v y) / (w - v))
      (k := k) tendsto_const_nhds hsq ?_ ?_ fun z => ?_
    · filter_upwards [hmem] with w hw
      have hw' : w ∈ Icc 0 a := ⟨hv.1.trans hw.1.1, hw.1.2⟩
      exact (((hcf w hw').sub (hcf v hv)).div_const _ |>.sub
        ((((continuous_heat (hcf v hv) (b0 v hv)).comp (Continuous.prodMk_right _)).sub
          (hcf v hv)).div_const _)).comp (by fun_prop) |>.aestronglyMeasurable
    · refine ⟨C + (C / 2 + C * T * Real.sqrt a), K, ?_⟩
      filter_upwards [hmem] with w hw y
      have hw' : w ∈ Icc 0 a := ⟨hv.1.trans hw.1.1, hw.1.2⟩
      have hwv : v < w := lt_of_le_of_ne hw.1.1 (Ne.symm hw.2)
      refine (abs_sub _ _).trans ?_
      have := sl_bound w hw' hw.2 y
      have := tq_bound v hv (w - v) (by linarith) (by linarith [hw.1.2, hv.1]) y
      linarith
    · have hy : Tendsto (fun w => x + Real.sqrt (a - w) * z) (𝓝[Icc v a \ {v}] v)
          (𝓝 (x + Real.sqrt (a - v) * z)) := tendsto_const_nhds.add (hsq.mul_const z)
      have hA := tendsto_slope_joint htime (hcont (v, _) ⟨hv, trivial⟩) hv
        (tendsto_nhdsWithin_mono_right hsub (tendsto_id (x := 𝓝[Icc v a \ {v}] v))) hy
      have hδ : Tendsto (fun w => w - v) (𝓝[Icc v a \ {v}] v) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have : Tendsto (fun w => w - v) (𝓝 v) (𝓝 (v - v)) :=
            tendsto_id.sub tendsto_const_nhds
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [hmem] with w hw
          exact sub_pos.2 (lt_of_le_of_ne hw.1.1 (Ne.symm hw.2))
      have hB := tendsto_heat_quotient (w := fun _ => v) (y := fun w => x + Real.sqrt (a - w) * z)
        hd₁ hd₂ hd₃ hK b0 b3 (.of_forall fun _ => hv) hδ
        (hmem.mono fun w hw => by linarith [hw.1.2, hv.1]) hy
        (((hc2 v hv).tendsto _).comp hy)
      exact hA.sub hB

end Heat

end

end SpinGlass.Aristotle
