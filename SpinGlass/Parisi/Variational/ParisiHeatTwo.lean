import SpinGlass.Parisi.Analytic.Heat.Jet
import Common.Mathlib.Probability.Distributions.Gaussian.HeatSemigroup

/-!
# Heat calculus with two spatial derivatives

The squared-curvature split moment uses four derivatives of its terminal
input. The backward heat formula here uses only two derivatives of the
integrand, so it does not require a fifth terminal derivative. Zero variance
is treated by the one-sided Gaussian heat equation.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace SpinGlass.Aristotle.Heat

/-- The forward heat equation with two input derivatives, including zero time. -/
theorem hasDerivWithinAt_heat_time_two {f f₁ f₂ : ℝ → ℝ}
    (hd₁ : ∀ y, HasDerivAt f (f₁ y) y)
    (hd₂ : ∀ y, HasDerivAt f₁ (f₂ y) y)
    (hb : ExpT f) (hb₁ : ExpT f₁) (hb₂ : ExpT f₂)
    (hc₂ : Continuous f₂) {a t : ℝ} (ht : t ∈ Icc 0 a) (y : ℝ) :
    HasDerivWithinAt (fun s => heat s f y) (heat t f₂ y / 2) (Icc 0 a) t := by
  have hg : ∀ {g : ℝ → ℝ}, ExpT g → HasExpGrowth g := by
    intro g h
    obtain ⟨C, K, _, hK, hbound⟩ := h.bound
    exact ⟨C, K, hK, hbound⟩
  rcases eq_or_lt_of_le ht.1 with hzero | hpos
  · subst t
    have h := hasDerivWithinAt_integral_comp_add_gaussianReal_var_zero
      hd₁ hd₂ (hg hb) (hg hb₁) (hg hb₂) hc₂ y
    rw [heat_zero hc₂]
    exact (h.mono fun s hs => hs.1).congr_deriv (by ring)
  · exact (hasDerivAt_integral_comp_add_gaussianReal_var
      hd₁ hd₂ (hg hb) (hg hb₁) (hg hb₂) hc₂ hpos y).hasDerivWithinAt.congr_deriv
        (by simp only [heat]; ring)

/-- Joint continuity of a Gaussian smoothing of a uniformly exponential family. -/
theorem continuousOn_heat_family {S : Set ℝ} {h : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => h p.1 p.2) (S ×ˢ univ))
    (hb : UExp S h) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => heat p.2.1 (h p.1) p.2.2)
      (S ×ˢ univ) := by
  obtain ⟨C, K, _, _, hbound⟩ := hb.nonneg
  have hspace : ∀ w ∈ S, Continuous (h w) := fun w hw =>
    hc.comp_continuous (Continuous.prodMk_right w) fun y => ⟨hw, trivial⟩
  intro p hp
  have hmem : ∀ᶠ q in 𝓝[S ×ˢ univ] p, q ∈ S ×ˢ univ := self_mem_nhdsWithin
  have hx : Tendsto (fun q : ℝ × (ℝ × ℝ) => q.2.2) (𝓝[S ×ˢ univ] p) (𝓝 p.2.2) :=
    (continuous_snd.comp continuous_snd).continuousAt.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun q : ℝ × (ℝ × ℝ) => Real.sqrt q.2.1)
      (𝓝[S ×ˢ univ] p) (𝓝 (Real.sqrt p.2.1)) :=
    (Real.continuous_sqrt.comp (continuous_fst.comp continuous_snd)).continuousAt.mono_left
      nhdsWithin_le_nhds
  have hlim := tendsto_integral_std (q := fun q => h q.1) (k := h p.1) hx hs
    (hmem.mono fun q hq => ((hspace q.1 hq.1).comp (by fun_prop)).aestronglyMeasurable)
    ⟨C, K, hmem.mono fun q hq => hbound q.1 hq.1⟩ (fun z => ?_)
  · change Tendsto (fun q : ℝ × (ℝ × ℝ) => heat q.2.1 (h q.1) q.2.2)
      (𝓝[S ×ˢ univ] p) (𝓝 (heat p.2.1 (h p.1) p.2.2))
    rw [heat_eq_std _ (hspace p.1 hp.1)]
    exact hlim.congr' (hmem.mono fun q hq => (heat_eq_std _ (hspace q.1 hq.1) _).symm)
  · have hpair : Tendsto (fun q : ℝ × (ℝ × ℝ) =>
        (q.1, q.2.2 + Real.sqrt q.2.1 * z)) (𝓝[S ×ˢ univ] p)
        (𝓝[S ×ˢ univ] (p.1, p.2.2 + Real.sqrt p.2.1 * z)) := by
      apply tendsto_nhdsWithin_iff.2
      refine ⟨?_, hmem.mono fun q hq => ⟨hq.1, trivial⟩⟩
      simpa only [nhds_prod_eq] using
        ((continuous_fst.continuousAt.mono_left nhdsWithin_le_nhds).prodMk
          (hx.add (hs.mul_const z)))
    exact (hc (p.1, p.2.2 + Real.sqrt p.2.1 * z) ⟨hp.1, trivial⟩).tendsto.comp hpair

/-- Four-jets have a time derivative also for their second component. -/
theorem Jet.heat_time_two {d : ℕ → ℝ → ℝ} (hd : Jet d) {j : ℕ} (hj : j ≤ 2)
    {a t : ℝ} (ht : t ∈ Icc 0 a) (y : ℝ) :
    HasDerivWithinAt (fun s => heat s (d j) y) (heat t (d (j + 2)) y / 2) (Icc 0 a) t :=
  hasDerivWithinAt_heat_time_two (hd.hasDeriv j (by omega))
    (hd.hasDeriv (j + 1) (by omega)) (hd.expT j (by omega))
    (hd.expT (j + 1) (by omega)) (hd.expT (j + 2) (by omega))
    (hd.continuous (by omega)) ht y

theorem hfam_time_two {g : ℕ → ℝ → ℝ} (hg : Jet g) {j : ℕ} (hj : j ≤ 2)
    {a w : ℝ} (hw : w ∈ Icc 0 a) (y : ℝ) :
    HasDerivWithinAt (fun u => hfam g j u y) (hfam g (j + 2) w y / 2) (Icc 0 a) w :=
  hg.heat_time_two hj hw y

/-- Heat difference quotients converge for moving C2 inputs and base points.
Joint continuity of the second derivative replaces a third derivative bound. -/
theorem tendsto_heat_quotient_two {a v : ℝ} (hv : v ∈ Icc 0 a)
    {h h₁ h₂ : ℝ → ℝ → ℝ}
    (hd₁ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h w) (h₁ w y) y)
    (hd₂ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h₁ w) (h₂ w y) y)
    (hb : UExp (Icc 0 a) h) (hb₁ : UExp (Icc 0 a) h₁)
    (hb₂ : UExp (Icc 0 a) h₂)
    (hc₂ : ContinuousOn (fun p : ℝ × ℝ => h₂ p.1 p.2) (Icc 0 a ×ˢ univ))
    {ι : Type*} {l : Filter ι} {w δ y : ι → ℝ} {y₀ : ℝ}
    (hw : Tendsto w l (𝓝[Icc 0 a] v)) (hδ : Tendsto δ l (𝓝[>] 0))
    (hδa : ∀ᶠ i in l, δ i ≤ a) (hy : Tendsto y l (𝓝 y₀)) :
    Tendsto (fun i => (heat (δ i) (h (w i)) (y i) - h (w i) (y i)) / δ i)
      l (𝓝 (h₂ v y₀ / 2)) := by
  have hspace : ∀ w ∈ Icc 0 a, Continuous (h₂ w) := fun w hw =>
    hc₂.comp_continuous (Continuous.prodMk_right w) fun z => ⟨hw, trivial⟩
  have htime : ∀ w ∈ Icc 0 a, ∀ t ∈ Icc 0 a, ∀ z,
      HasDerivWithinAt (fun s => heat s (h w) z) (heat t (h₂ w) z / 2) (Icc 0 a) t := by
    intro w hw t ht z
    apply hasDerivWithinAt_heat_time_two (hd₁ w hw) (hd₂ w hw)
    · obtain ⟨C, K, h⟩ := hb
      exact ⟨C, K, fun _ _ => h w hw⟩
    · obtain ⟨C, K, h⟩ := hb₁
      exact ⟨C, K, fun _ _ => h w hw⟩
    · obtain ⟨C, K, h⟩ := hb₂
      exact ⟨C, K, fun _ _ => h w hw⟩
    · exact hspace w hw
    · exact ht
  have hc := (continuousOn_heat_family hc₂ hb₂).div_const 2
  have hc0 := hc (v, (0, y₀)) ⟨hv, trivial⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := Metric.continuousWithinAt_iff.1 hc0 (ε / 2) (half_pos hε)
  simp only [heat_zero (hspace v hv)] at hηε
  have hwmem : ∀ᶠ i in l, w i ∈ Icc 0 a := hw self_mem_nhdsWithin
  have hwη : ∀ᶠ i in l, dist (w i) v < η :=
    (tendsto_nhdsWithin_iff.1 hw).1 (Metric.ball_mem_nhds v hη)
  have hyη : ∀ᶠ i in l, dist (y i) y₀ < η := hy (Metric.ball_mem_nhds y₀ hη)
  have hδ0 := (tendsto_nhdsWithin_iff.1 hδ).1
  have hδη : ∀ᶠ i in l, δ i < η := hδ0 (gt_mem_nhds hη)
  filter_upwards [hwmem, hwη, hyη, hδ self_mem_nhdsWithin, hδη, hδa]
    with i hwi hwiη hyiη hδi hδiη hδia
  change 0 < δ i at hδi
  set c := h₂ v y₀ / 2
  have hsub : Icc (0 : ℝ) (δ i) ⊆ Icc 0 a := Icc_subset_Icc le_rfl hδia
  have hbound := (convex_Icc (0 : ℝ) (δ i)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => heat t (h (w i)) (y i) - t * c)
    (f' := fun t => heat t (h₂ (w i)) (y i) / 2 - c) (C := ε / 2)
    (fun t ht => ((htime (w i) hwi t (hsub ht) (y i)).mono hsub).sub
      ((hasDerivWithinAt_id t _).mul_const c) |>.congr_deriv (by simp))
    (fun t ht => by
      have hp : (w i, (t, y i)) ∈ Icc 0 a ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hwi, trivial⟩
      have hd : dist (w i, (t, y i)) (v, (0, y₀)) < η := by
        simp only [Prod.dist_eq, max_lt_iff]
        refine ⟨hwiη, ?_, hyiη⟩
        rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
        exact ht.2.trans_lt hδiη
      have := hηε hp hd
      rw [Real.dist_eq] at this
      exact this.le)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) (δ i) from ⟨le_rfl, hδi.le⟩)
    (show δ i ∈ Icc (0 : ℝ) (δ i) from ⟨hδi.le, le_rfl⟩)
  have hh : Continuous (h (w i)) := continuous_iff_continuousAt.2 fun z =>
    (hd₁ (w i) hwi z).continuousAt
  rw [heat_zero hh] at hbound
  rw [Real.dist_eq]
  have he : (heat (δ i) (h (w i)) (y i) - h (w i) (y i)) / δ i - c =
      ((heat (δ i) (h (w i)) (y i) - δ i * c) - (h (w i) (y i) - 0 * c)) / δ i := by
    field_simp [ne_of_gt hδi]
    ring
  rw [he, abs_div, show |δ i| = δ i from abs_of_pos hδi, div_lt_iff₀ hδi]
  simp only [Real.norm_eq_abs, sub_zero, abs_of_pos hδi] at hbound
  exact hbound.trans_lt (by nlinarith)

/-- Backward heat differentiation for a C2 integrand family on the closed variance interval. -/
theorem hasDerivWithinAt_heat_backward_two {a x v : ℝ} (hv : v ∈ Icc 0 a)
    {h h₁ h₂ hv' : ℝ → ℝ → ℝ}
    (hd₁ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h w) (h₁ w y) y)
    (hd₂ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h₁ w) (h₂ w y) y)
    (hb : UExp (Icc 0 a) h) (hb₁ : UExp (Icc 0 a) h₁) (hb₂ : UExp (Icc 0 a) h₂)
    (hbv : UExp (Icc 0 a) hv')
    (htime : ∀ y, ∀ w ∈ Icc 0 a, HasDerivWithinAt (fun u => h u y) (hv' w y) (Icc 0 a) w)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => hv' p.1 p.2) (Icc 0 a ×ˢ univ))
    (hcont₂ : ContinuousOn (fun p : ℝ × ℝ => h₂ p.1 p.2) (Icc 0 a ×ˢ univ)) :
    HasDerivWithinAt (fun w => heat (a - w) (h w) x)
      (heat (a - v) (fun y => hv' v y - h₂ v y / 2) x) (Icc 0 a) v := by
  obtain ⟨C, K, hC, hK, hB⟩ := (((hb.abs.add hb₁.abs).add hb₂.abs).add hbv.abs).nonneg
  have b0 : ∀ w ∈ Icc 0 a, ∀ y, |h w y| ≤ C * Real.exp (K * |y|) := fun w hw y => by
    have := hB w hw y; rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (h₂ w y), abs_nonneg (h₁ w y), abs_nonneg (hv' w y)]
  have b2 : ∀ w ∈ Icc 0 a, ∀ y, |h₂ w y| ≤ C * Real.exp (K * |y|) := fun w hw y => by
    have := hB w hw y; rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (h w y), abs_nonneg (h₁ w y), abs_nonneg (hv' w y)]
  have b1 : ∀ w ∈ Icc 0 a, ∀ y, |h₁ w y| ≤ C * Real.exp (K * |y|) := fun w hw y => by
    have := hB w hw y; rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (h w y), abs_nonneg (h₂ w y), abs_nonneg (hv' w y)]
  have bv : ∀ w ∈ Icc 0 a, ∀ y, |hv' w y| ≤ C * Real.exp (K * |y|) := fun w hw y => by
    have := hB w hw y; rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (h w y), abs_nonneg (h₂ w y), abs_nonneg (h₁ w y)]
  have hcf : ∀ w ∈ Icc 0 a, Continuous (h w) := fun w hw =>
    continuous_iff_continuousAt.2 fun y => (hd₁ w hw y).continuousAt
  have hc2 : ∀ w ∈ Icc 0 a, Continuous (h₂ w) := fun w hw =>
    hcont₂.comp_continuous (Continuous.prodMk_right w) fun y => ⟨hw, trivial⟩
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
  set Z := ∫ z : ℝ, Real.exp (K * Real.sqrt a * |z|) ∂gaussianReal 0 1
  have tq_bound : ∀ w ∈ Icc 0 a, ∀ δ, 0 < δ → δ ≤ a → ∀ y,
      |(heat δ (h w) y - h w y) / δ| ≤ (C * Z / 2) * Real.exp (K * |y|) := by
    intro w hw δ hδ hδa y
    have ht : ∀ z, ∀ t ∈ Icc 0 a,
        HasDerivWithinAt (fun u => heat u (h w) z)
          (heat t (h₂ w) z / 2) (Icc 0 a) t := by
      intro z t ht
      exact hasDerivWithinAt_heat_time_two (hd₁ w hw) (hd₂ w hw)
        ⟨C, K, fun _ _ => b0 w hw⟩ ⟨C, K, fun _ _ => b1 w hw⟩
        ⟨C, K, fun _ _ => b2 w hw⟩ (hc2 w hw) ht z
    have hbt : ∀ t ∈ Icc 0 a, ∀ z,
        |heat t (h₂ w) z / 2| ≤ (C * Z / 2) * Real.exp (K * |z|) := by
      intro t ht z
      rw [abs_div, abs_two]
      have hh := abs_heat_le (hc2 w hw) hK (b2 w hw) ht.2 z
      exact (div_le_div_of_nonneg_right hh (by norm_num)).trans_eq (by dsimp [Z]; ring)
    have hh := abs_sub_le_of_time ht hbt (show (0 : ℝ) ∈ Icc 0 a from
      ⟨le_rfl, hv.1.trans hv.2⟩) ⟨hδ.le, hδa⟩ y
    rw [heat_zero (hcf w hw), sub_zero, abs_of_pos hδ] at hh
    rw [abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
    exact hh
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
    · refine ⟨C + (C * Z / 2), K, ?_⟩
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
      have hB := tendsto_heat_quotient_two hv hd₁ hd₂ hb hb₁ hb₂ hcont₂
        (w := fun w => w) (y := fun _ => x + Real.sqrt (a - v) * z)
        (tendsto_nhdsWithin_mono_right (hsub.trans sdiff_subset)
          (tendsto_id (x := 𝓝[Icc 0 v \ {v}] v))) hδ
        (hmem.mono fun w hw => by linarith [hw.1.1, hv.2]) tendsto_const_nhds
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
    · refine ⟨C + (C * Z / 2), K, ?_⟩
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
      have hB := tendsto_heat_quotient_two hv hd₁ hd₂ hb hb₁ hb₂ hcont₂
        (w := fun _ => v) (y := fun w => x + Real.sqrt (a - w) * z)
        (tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds, .of_forall fun _ => hv⟩) hδ
        (hmem.mono fun w hw => by linarith [hw.1.2, hv.1]) hy
      exact hA.sub hB


end SpinGlass.Aristotle.Heat
