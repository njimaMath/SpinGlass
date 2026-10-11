import SpinGlass.Parisi.Minimizer.Compact
import SpinGlass.Parisi.Variational.ParisiMassDerivative

/-!
# Mass coordinates of the concrete closed Parisi recursion

The mass coordinate is varied in the actual finite recursion. Its derivative
is transported by the preceding cascade tilt and averaged over the site field
and the independent root Gaussian, as in (14.234)-(14.240).
-/

open MeasureTheory ProbabilityTheory Set
open Filter Topology
open scoped NNReal ENNReal BigOperators

namespace SpinGlass

private lemma fin_append_one_slices {α : Type} (i s : ℕ)
    (a : Fin (i + (s + 1)) → α) :
    Fin.append (fun p : Fin i => a ⟨p.val, by omega⟩)
      (Fin.cons (a ⟨i, by omega⟩) (fun p : Fin s => a ⟨i + p.val + 1, by omega⟩)) = a := by
  funext p
  refine Fin.addCases (fun q => ?_) (fun q => ?_) p
  · simp only [Fin.append_left]
    congr 1
  · refine Fin.cases ?_ (fun t => ?_) q
    · simp only [Fin.append_right, Fin.cons_zero]
      congr 1
    · simp only [Fin.append_right, Fin.cons_succ]
      apply congrArg a
      apply Fin.ext
      simp
      omega

/-- Split at a single varied mass, without requiring an adjacent level. -/
theorem coleHopfIterate_split_one_of_eq {n : ℕ} (i s : ℕ) (hn : n = i + (s + 1))
    (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0) (G : ℝ → ℝ) :
    coleHopfIterate n ms vs G =
      coleHopfIterate i
        (fun p => ms ⟨p.val, by omega⟩) (fun p => vs ⟨p.val, by omega⟩)
        (coleHopf (ms ⟨i, by omega⟩) (vs ⟨i, by omega⟩)
          (coleHopfIterate s
            (fun p => ms ⟨i + p.val + 1, by omega⟩)
            (fun p => vs ⟨i + p.val + 1, by omega⟩) G)) := by
  subst n
  conv_lhs =>
    rw [← fin_append_one_slices i s ms, ← fin_append_one_slices i s vs]
  rw [coleHopfIterate_append, coleHopfIterate_succ]
  simp only [Fin.cons_zero, Fin.tail_cons]

/-- The fixed masses preceding the coordinate represented by `r`. -/
def parisiMassPrefixMasses {k : ℕ} (ms : Fin k → ℝ) (r : Fin k) :
    Fin r.val → ℝ := fun p => ms ⟨p.val, by omega⟩

/-- The fixed variances preceding the coordinate represented by `r`. -/
noncomputable def parisiMassPrefixVars (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (r : Fin k) : Fin r.val → ℝ≥0 :=
  fun p => parisiVar ξ qs (p.val + 1)

/-- Updating one mass affects exactly one layer of the closed recursion.
The identity also holds at zero mass, independently of admissibility. -/
theorem closedParisiX₀_mass_update_eq (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin k) (m h : ℝ) :
    closedParisiX₀ ξ (Function.update ms r m) qs h =
      ∫ z₀, coleHopfIterate r.val (parisiMassPrefixMasses ms r)
        (parisiMassPrefixVars ξ qs r)
        (coleHopf m (parisiVar ξ qs (r.val + 1))
          (parisiQSuffix ξ 0 ms qs r.castSucc)) (h + z₀)
        ∂gaussianReal 0 (parisiVar ξ qs 0) := by
  have hn : k + 1 = r.val + ((k - r.val) + 1) := by omega
  have hi : coleHopfIterate (k + 1) (parisiLevelMasses (Function.update ms r m))
      (parisiLevelVars ξ qs) (parisiLogCoshTerminal 0) =
      coleHopfIterate r.val (parisiMassPrefixMasses ms r)
        (parisiMassPrefixVars ξ qs r)
        (coleHopf m (parisiVar ξ qs (r.val + 1))
          (parisiQSuffix ξ 0 ms qs r.castSucc)) := by
    rw [coleHopfIterate_split_one_of_eq r.val (k - r.val) hn]
    congr 3
    · funext p
      rw [parisiLevelMasses_apply]
      change mExt (Function.update ms r m) (p.val + 1) = ms ⟨p.val, by omega⟩
      rw [mExt_val_succ _ (⟨p.val, by omega⟩ : Fin k)]
      have hpne : (⟨p.val, by omega⟩ : Fin k) ≠ r := by
        intro he
        have hv := congrArg Fin.val he
        change p.val = r.val at hv
        omega
      exact Function.update_of_ne hpne m ms
    · rw [parisiLevelMasses_apply]
      change mExt (Function.update ms r m) (r.val + 1) = m
      rw [mExt_val_succ _ r, Function.update_self]
    · funext p
      rw [parisiLevelMasses_apply]
      change mExt (Function.update ms r m) (r.val + p.val + 1 + 1) =
        mExt ms (r.val + p.val + 2)
      have hidx : r.val + p.val + 1 + 1 = r.val + p.val + 2 := by omega
      rw [hidx]
      by_cases hp : r.val + p.val + 1 < k
      · let t : Fin k := ⟨r.val + p.val + 1, hp⟩
        rw [mExt_val_succ _ t, mExt_val_succ _ t]
        have htne : t ≠ r := by
          intro he
          have hv := congrArg Fin.val he
          change r.val + p.val + 1 = r.val at hv
          omega
        exact Function.update_of_ne htne m ms
      · rw [mExt_eq_one_of_le _ (by omega), mExt_eq_one_of_le _ (by omega)]
  rw [closedParisiX₀_translate, coleHopfIterate_succ]
  change coleHopf 0 (parisiVar ξ qs 0)
      (coleHopfIterate (k + 1) (parisiLevelMasses (Function.update ms r m))
        (parisiLevelVars ξ qs) (parisiLogCoshTerminal 0)) h = _
  rw [hi, coleHopf_zero]

/-- The derivative of a concrete mass coordinate of the averaged root value. -/
noncomputable def randomFieldParisiMassMoment (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin k) (m : ℝ) : ℝ :=
  ∫ h, ∫ z₀, coleHopfIterateMassDeriv (parisiMassPrefixMasses ms r)
    (parisiMassPrefixVars ξ qs r) (parisiVar ξ qs (r.val + 1))
    (parisiQSuffix ξ 0 ms qs r.castSucc) m (h + z₀)
    ∂gaussianReal 0 (parisiVar ξ qs 0) ∂μh

/-- Concrete mass differentiation under the root Gaussian and field law.
Only preceding masses need to be positive; the varied mass may be zero.
This supplies the averaged recursion derivative used in (14.238)-(14.240). -/
theorem hasDerivWithinAt_randomFieldParisiX₀_mass_update
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin k)
    (hpos : ∀ p : Fin r.val, 0 < ms ⟨p.val, by omega⟩)
    (hle : ∀ p : Fin r.val, ms ⟨p.val, by omega⟩ ≤ 1)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun b => ∫ h, closedParisiX₀ ξ (Function.update ms r b) qs h ∂μh)
      (randomFieldParisiMassMoment μh ξ ms qs r m) (Icc (0 : ℝ) 1) m := by
  have hLip := abs_parisiQSuffix_sub_le ξ 0 ms qs r.castSucc
  have hAm := (lipschitzWith_toNNReal_of_abs_sub_le
    (L := 1) (by simpa only [one_mul] using hLip)).continuous.measurable
  simpa only [closedParisiX₀_mass_update_eq, randomFieldParisiMassMoment] using
    hasDerivWithinAt_integral_integral_coleHopfIterate_mass_layer hμ
      (parisiMassPrefixMasses ms r) (parisiMassPrefixVars ξ qs r) hpos hle
      hAm hLip (parisiVar ξ qs (r.val + 1)) (parisiVar ξ qs 0) hm

/-- The extended mass sequence changes at exactly its chosen free coordinate. -/
theorem mExt_mass_update_succ {k : ℕ} (ms : Fin k → ℝ) (r : Fin k) (m : ℝ) (p : ℕ) :
    mExt (Function.update ms r m) (p + 1) =
      if p = r.val then m else mExt ms (p + 1) := by
  by_cases hp : p < k
  · let t : Fin k := ⟨p, hp⟩
    rw [mExt_val_succ _ t, mExt_val_succ _ t]
    by_cases hpr : p = r.val
    · have ht : t = r := Fin.ext hpr
      simp only [ht, Function.update_self, hpr, ite_true]
    · have ht : t ≠ r := fun he => hpr (congrArg Fin.val he)
      rw [Function.update_of_ne ht, ite_eq_right hpr]
  · have hpr : p ≠ r.val := by intro he; subst p; exact hp r.isLt
    rw [mExt_eq_one_of_le _ (by omega), mExt_eq_one_of_le _ (by omega), ite_eq_right hpr]

/-- A mass update changes only the linear correction associated with its
Gaussian interval. This is the correction term differentiated in (14.236). -/
theorem parisiMassPenalty_mass_update_eq (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin k) (m : ℝ) :
    (∑ p ∈ Finset.range (k + 1), mExt (Function.update ms r m) (p + 1) *
      (parisiTheta ξ (qExt qs (p + 2)) - parisiTheta ξ (qExt qs (p + 1)))) =
    (∑ p ∈ (Finset.range (k + 1)).erase r.val, mExt ms (p + 1) *
      (parisiTheta ξ (qExt qs (p + 2)) - parisiTheta ξ (qExt qs (p + 1)))) +
    m * (parisiTheta ξ (qExt qs (r.val + 2)) - parisiTheta ξ (qExt qs (r.val + 1))) := by
  have hr : r.val ∈ Finset.range (k + 1) := Finset.mem_range.2 (by omega)
  rw [← Finset.sum_erase_add _ _ hr, mExt_mass_update_succ, ite_eq_left (rfl : r.val = r.val)]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [mExt_mass_update_succ, ite_eq_right (Finset.mem_erase.1 hp).1]

/-- The actual closed random-field Parisi functional is differentiable in each
mass coordinate on `[0,1]`, including one-sided endpoint derivatives. The
derivative is the concrete cascade moment minus the explicit theta correction.
Together with the split constructors this is the mass derivative in (14.230). -/
theorem hasDerivWithinAt_closedRandomFieldParisiFunctional_mass_update
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin k)
    (hpos : ∀ p : Fin r.val, 0 < ms ⟨p.val, by omega⟩)
    (hle : ∀ p : Fin r.val, ms ⟨p.val, by omega⟩ ≤ 1)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun b => closedRandomFieldParisiFunctional μh ξ (Function.update ms r b) qs)
      (randomFieldParisiMassMoment μh ξ ms qs r m - (1 / 2) *
        (parisiTheta ξ (qExt qs (r.val + 2)) - parisiTheta ξ (qExt qs (r.val + 1))))
      (Icc (0 : ℝ) 1) m := by
  let C := ∑ p ∈ (Finset.range (k + 1)).erase r.val, mExt ms (p + 1) *
    (parisiTheta ξ (qExt qs (p + 2)) - parisiTheta ξ (qExt qs (p + 1)))
  let d := parisiTheta ξ (qExt qs (r.val + 2)) - parisiTheta ξ (qExt qs (r.val + 1))
  have hfun : (fun b => closedRandomFieldParisiFunctional μh ξ (Function.update ms r b) qs) =
      fun b => Real.log 2 + (∫ h, closedParisiX₀ ξ (Function.update ms r b) qs h ∂μh) -
        (1 / 2) * (C + b * d) := by
    funext b
    unfold closedRandomFieldParisiFunctional
    rw [parisiMassPenalty_mass_update_eq]
  have hlin : HasDerivAt (fun b => C + b * d) d m := by
    simpa only [id_eq, one_mul] using ((hasDerivAt_id m).mul_const d).const_add C
  rw [hfun]
  exact (hasDerivWithinAt_randomFieldParisiX₀_mass_update hμ ξ ms qs r hpos hle hm
    |>.const_add (Real.log 2)).sub ((hlin.const_mul (1 / 2)).hasDerivWithinAt)

/-- A strict mass vector admits a whole neighborhood of each coordinate
variation. This is the admissibility needed for fixed-level mass stationarity. -/
theorem ParisiMAdmissible.eventually_mass_update {k : ℕ} {ms : Fin k → ℝ}
    (hm : ParisiMAdmissible ms) (p : Fin k) :
    ∀ᶠ b in 𝓝 (ms p), ParisiMAdmissible (Function.update ms p b) := by
  have hval (i : Fin k) : Continuous (fun b : ℝ => Function.update ms p b i) := by
    by_cases hi : i = p
    · subst i
      simp only [Function.update_self]
      exact continuous_id
    · simpa only [Function.update_of_ne hi] using (continuous_const (y := ms i))
  have hmono : ∀ i j : Fin k, ∀ᶠ b in 𝓝 (ms p),
      i < j → Function.update ms p b i < Function.update ms p b j := by
    intro i j
    by_cases hij : i < j
    · have hlt : Function.update ms p (ms p) i < Function.update ms p (ms p) j := by
        simpa only [Function.update_eq_self] using hm.1 hij
      exact ((hval i).continuousAt.eventually_lt (hval j).continuousAt hlt).mono
        fun b hb _ => hb
    · exact .of_forall fun b hij' => (hij hij').elim
  have hpos : ∀ i : Fin k, ∀ᶠ b in 𝓝 (ms p), 0 < Function.update ms p b i := by
    intro i
    apply continuousAt_const.eventually_lt (hval i).continuousAt
    simpa only [Function.update_eq_self] using hm.2.1 i
  have hle : ∀ i : Fin k, ∀ᶠ b in 𝓝 (ms p), Function.update ms p b i < 1 := by
    intro i
    apply (hval i).continuousAt.eventually_lt continuousAt_const
    simpa only [Function.update_eq_self] using hm.2.2 i
  filter_upwards [eventually_all.2 (fun i => eventually_all.2 (hmono i)),
    eventually_all.2 hpos, eventually_all.2 hle] with b hb hp hl
  exact ⟨hb, hp, hl⟩

/-- A closed fixed-level MIN is a local minimum of every mass coordinate
when its original masses are strict. No comparison across dimensions is used. -/
theorem isLocalMin_closedRandomFieldParisiFunctional_mass_update_of_isMinOn
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : qs ∈ parisiOverlapDomain k)
    (hmin : IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain k) (ms, qs)) :
    IsLocalMin (fun b => closedRandomFieldParisiFunctional μh ξ (Function.update ms p b) qs)
      (ms p) := by
  filter_upwards [hm.eventually_mass_update p] with b hb
  have hmem : (Function.update ms p b, qs) ∈ parisiParameterDomain k := by
    exact ⟨mem_parisiMassDomain_iff.2 ⟨hb.1.monotone,
      (fun i => (hb.2.1 i).le), (fun i => (hb.2.2 i).le)⟩, hq⟩
  simpa using hmin hmem

/-- Fixed-level mass minimality forces the actual mass derivative to vanish.
This is the stationarity used at the left endpoint in (14.242). -/
theorem randomFieldParisiMassMoment_sub_theta_eq_zero_of_isMinOn
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : qs ∈ parisiOverlapDomain k)
    (hmin : IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain k) (ms, qs)) :
    randomFieldParisiMassMoment μh ξ ms qs p (ms p) - (1 / 2) *
      (parisiTheta ξ (qExt qs (p.val + 2)) - parisiTheta ξ (qExt qs (p.val + 1))) = 0 := by
  have hd := (hasDerivWithinAt_closedRandomFieldParisiFunctional_mass_update hμ ξ ms qs p
    (fun r => hm.2.1 _) (fun r => (hm.2.2 _).le) ⟨(hm.2.1 p).le, (hm.2.2 p).le⟩).hasDerivAt
      (Icc_mem_nhds (hm.2.1 p) (hm.2.2 p))
  have hlocal :=
    isLocalMin_closedRandomFieldParisiFunctional_mass_update_of_isMinOn μh ξ ms qs p hm hq hmin
  exact hd.deriv.symm.trans hlocal.deriv_eq_zero

end SpinGlass
