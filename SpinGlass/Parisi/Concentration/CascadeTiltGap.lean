import SpinGlass.Parisi.Tree.CascadeLogIntegrable
import Common.Mathlib.Probability.PointProcess.CascadeTiltMeasure

/-!
# A constrained cascade pressure controls its tilted mass

This is the recursive inequality underlying (14.120). The observable
is the actual cascade tilted average of the constrained partition ratio.
It includes an empty constraint and zero levels. Positive lower bounds
on the masses enter only through the explicit exponent.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace SpinGlass

/-- Talagrand's downward recursion (14.120), before taking logarithms.
Every lower bound on the positive masses gives an admissible exponent.
The unconstrained partition function is finite and positive at every mark,
and its product integral is finite. The constraint may be empty. -/
theorem cascadeTilt_div_le_cascadeRec_ratio_rpow {T : Type*} [MeasurableSpace T]
    (k : ℕ) : ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)]
    {G A : (Fin k → T) → ℝ≥0∞},
    Measurable G → Measurable A → (∀ zs, 0 < G zs) → (∀ zs, G zs ≠ ∞) →
    (∀ zs, A zs ≤ G zs) → Monotone ms → (∀ i, 0 < ms i) → (∀ i, ms i ≤ 1) →
    (∫⁻ zs, G zs ∂Measure.pi μs) ≠ ∞ →
    ∀ a : ℝ, 0 < a → a ≤ 1 → (∀ i, a ≤ ms i) →
      cascadeTilt k ms μs G (fun zs => A zs / G zs) ≤
        (cascadeRec k ms μs A / cascadeRec k ms μs G) ^ a := by
  induction k with
  | zero =>
    intro ms μs _ G A hG hA hGpos hGfinite hAG hmono hpos hle hfin a ha ha1 halower
    simp only [cascadeTilt_zero, cascadeRec_zero]
    have hratio : A Fin.elim0 / G Fin.elim0 ≤ 1 := by
      calc
        _ ≤ G Fin.elim0 / G Fin.elim0 := ENNReal.div_le_div_right (hAG _) _
        _ = 1 := ENNReal.div_self (hGpos _).ne' (hGfinite _)
    simpa only [ENNReal.rpow_one] using
      (ENNReal.rpow_le_rpow_of_exponent_ge hratio ha1)
  | succ k ih =>
    intro ms μs _ G A hG hA hGpos hGfinite hAG hmono hpos hle hfin a ha ha1 halower
    let R := cascadeRec (k + 1) ms μs G
    let S := cascadeRec (k + 1) ms μs A
    let Rtail := fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
      (fun zs => G (Fin.cons z zs))
    let Stail := fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
      (fun zs => A (Fin.cons z zs))
    have hR0 : R ≠ 0 := (cascadeRec_pos _ _ _ hG hGpos hpos).ne'
    have hRtop : R ≠ ∞ := cascadeRec_ne_top _ _ _ hG hpos hle hfin
    have hratio : S / R ≤ 1 := by
      calc
        _ ≤ R / R := ENNReal.div_le_div_right
          (cascadeRec_mono _ _ _ hAG (fun i => (hpos i).le)) _
        _ = 1 := ENNReal.div_self hR0 hRtop
    have htailMono : Monotone (Fin.tail ms) := fun i j hij => hmono (by simpa using hij)
    have hmajor : ∀ᵐ z ∂μs 0,
        cascadeW k ms μs G z *
          cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
            (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs)) ≤
              Stail z ^ ms 0 / R ^ ms 0 := by
      filter_upwards [ae_lintegral_pi_cons_ne_top k μs hG hfin] with z hz
      have hGz : Measurable (fun zs : Fin k → T => G (Fin.cons z zs)) :=
        hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id))
      have hAz : Measurable (fun zs : Fin k → T => A (Fin.cons z zs)) :=
        hA.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id))
      have ht := ih (Fin.tail ms) (Fin.tail μs) hGz hAz
        (fun zs => hGpos _) (fun zs => hGfinite _) (fun zs => hAG _) htailMono
        (fun i => hpos i.succ) (fun i => hle i.succ) hz (ms 0) (hpos 0) (hle 0)
        (fun i => hmono (Fin.zero_le _))
      have hRt0 : Rtail z ≠ 0 := (cascadeRec_pos _ _ _ hGz
        (fun zs => hGpos _) (fun i => hpos i.succ)).ne'
      have hRttop : Rtail z ≠ ∞ := cascadeRec_ne_top _ _ _ hGz
        (fun i => hpos i.succ) (fun i => hle i.succ) hz
      have hpow0 : Rtail z ^ ms 0 ≠ 0 :=
        (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hRt0) (hpos 0).le).ne'
      have hpowtop : Rtail z ^ ms 0 ≠ ∞ :=
        ENNReal.rpow_ne_top_of_nonneg (hpos 0).le hRttop
      calc
        _ ≤ cascadeW k ms μs G z * (Stail z / Rtail z) ^ ms 0 :=
          mul_le_mul' le_rfl ht
        _ = (Rtail z ^ ms 0 / R ^ ms 0) * (Stail z ^ ms 0 / Rtail z ^ ms 0) := by
          rw [cascadeW, ENNReal.div_rpow_of_nonneg _ _ (hpos 0).le,
            ENNReal.div_rpow_of_nonneg _ _ (hpos 0).le]
        _ = (Stail z ^ ms 0 / R ^ ms 0) *
            (Rtail z ^ ms 0 * (Rtail z ^ ms 0)⁻¹) := by
          simp only [div_eq_mul_inv]
          calc
            _ = (Rtail z ^ ms 0 * Stail z ^ ms 0) *
                ((R ^ ms 0)⁻¹ * (Rtail z ^ ms 0)⁻¹) :=
              mul_mul_mul_comm _ _ _ _
            _ = (Stail z ^ ms 0 * Rtail z ^ ms 0) *
                ((R ^ ms 0)⁻¹ * (Rtail z ^ ms 0)⁻¹) := by rw [mul_comm (Rtail z ^ ms 0)]
            _ = _ := (mul_mul_mul_comm _ _ _ _).symm
        _ = _ := by rw [ENNReal.mul_inv_cancel hpow0 hpowtop, mul_one]
    rw [cascadeTilt_succ]
    calc
      _ ≤ ∫⁻ z, Stail z ^ ms 0 / R ^ ms 0 ∂μs 0 := lintegral_mono_ae hmajor
      _ = (S / R) ^ ms 0 := by
        rw [ENNReal.div_rpow_of_nonneg _ _ (hpos 0).le]
        simp only [div_eq_mul_inv]
        rw [lintegral_mul_const _ ((measurable_cascadeRec_cons k _ _ hA).pow_const _)]
        rw [← cascadeRec_rpow_eq_lintegral k ms μs A (hpos 0)]
      _ ≤ (S / R) ^ a := ENNReal.rpow_le_rpow_of_exponent_ge hratio (halower 0)

/-- A strictly positive terminal observable has strictly positive
average under the actual tilted probability measure. -/
theorem cascadeTilt_pos_of_pos {T : Type*} [MeasurableSpace T] {k : ℕ}
    (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
    {G B : (Fin k → T) → ℝ≥0∞} (hG : Measurable G) (hB : Measurable B)
    (hGpos : ∀ zs, 0 < G zs) (hBpos : ∀ zs, 0 < B zs)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hfin : (∫⁻ zs, G zs ∂Measure.pi μs) ≠ ∞) :
    0 < cascadeTilt k ms μs G B := by
  let := isProbabilityMeasure_cascadeTiltMeasure k ms μs hG hGpos hpos hle hfin
  rw [← lintegral_cascadeTiltMeasure k ms μs hG hB, lintegral_pos_iff_support hB]
  have hs : Function.support B = univ := eq_univ_of_forall fun zs => (hBpos zs).ne'
  rw [hs, measure_univ]
  exact zero_lt_one

/-- The constrained tilted mass is at most one, with no nonemptiness
assumption on the constraint. -/
theorem cascadeTilt_div_le_one {T : Type*} [MeasurableSpace T] {k : ℕ}
    (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
    {G A : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (hGpos : ∀ zs, 0 < G zs) (hGfinite : ∀ zs, G zs ≠ ∞) (hAG : ∀ zs, A zs ≤ G zs)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hfin : (∫⁻ zs, G zs ∂Measure.pi μs) ≠ ∞) :
    cascadeTilt k ms μs G (fun zs => A zs / G zs) ≤ 1 := by
  calc
    _ ≤ cascadeTilt k ms μs G (fun _ => 1) := cascadeTilt_mono k ms μs G fun zs => by
      calc
        A zs / G zs ≤ G zs / G zs := ENNReal.div_le_div_right (hAG zs) _
        _ = 1 := ENNReal.div_self (hGpos zs).ne' (hGfinite zs)
    _ = 1 := cascadeTilt_one k ms μs hG hGpos hpos hle hfin

/-- The logarithmic form of (14.120) at the initial level. For a
nonempty constraint the actual logarithm is finite, so averaging this
inequality gives the negative mean in (14.121). -/
theorem log_cascadeTilt_div_le_cascadeRec_gap {T : Type*} [MeasurableSpace T] {k : ℕ}
    (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
    {G A : (Fin k → T) → ℝ≥0∞} (hG : Measurable G) (hA : Measurable A)
    (hGpos : ∀ zs, 0 < G zs) (hApos : ∀ zs, 0 < A zs)
    (hGfinite : ∀ zs, G zs ≠ ∞) (hAG : ∀ zs, A zs ≤ G zs)
    (hmono : Monotone ms) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hfin : (∫⁻ zs, G zs ∂Measure.pi μs) ≠ ∞)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (halower : ∀ i, a ≤ ms i) :
    Real.log (cascadeTilt k ms μs G (fun zs => A zs / G zs)).toReal ≤
      a * (Real.log (cascadeRec k ms μs A).toReal -
        Real.log (cascadeRec k ms μs G).toReal) := by
  have hRG0 := (cascadeRec_pos k ms μs hG hGpos hpos).ne'
  have hRGtop := cascadeRec_ne_top k ms μs hG hpos hle hfin
  have hRA0 := (cascadeRec_pos k ms μs hA hApos hpos).ne'
  have hRAG := cascadeRec_mono k ms μs hAG (fun i => (hpos i).le)
  have hRAtop := ne_top_of_le_ne_top hRGtop hRAG
  have hratio : cascadeRec k ms μs A / cascadeRec k ms μs G ≤ 1 := by
    calc
      _ ≤ cascadeRec k ms μs G / cascadeRec k ms μs G :=
        ENNReal.div_le_div_right hRAG _
      _ = 1 := ENNReal.div_self hRG0 hRGtop
  have hratioTop := ne_top_of_le_ne_top ENNReal.one_ne_top hratio
  have hratioPos : 0 < (cascadeRec k ms μs A / cascadeRec k ms μs G).toReal := by
    rw [ENNReal.toReal_div]
    exact div_pos (ENNReal.toReal_pos hRA0 hRAtop) (ENNReal.toReal_pos hRG0 hRGtop)
  have hmassPos := cascadeTilt_pos_of_pos ms μs hG (hA.div hG) hGpos
    (fun zs => ENNReal.div_pos (hApos zs).ne' (hGfinite zs)) hpos hle hfin
  have hmassTop := ne_top_of_le_ne_top ENNReal.one_ne_top
    (cascadeTilt_div_le_one ms μs hG hGpos hGfinite hAG hpos hle hfin)
  have hb := cascadeTilt_div_le_cascadeRec_ratio_rpow k ms μs hG hA hGpos hGfinite
    hAG hmono hpos hle hfin a ha ha1 halower
  have hl := Real.log_le_log (ENNReal.toReal_pos hmassPos.ne' hmassTop)
    (ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg ha.le hratioTop) hb)
  rw [← ENNReal.toReal_rpow, Real.log_rpow hratioPos, ENNReal.toReal_div,
    Real.log_div (ENNReal.toReal_pos hRA0 hRAtop).ne'
      (ENNReal.toReal_pos hRG0 hRGtop).ne'] at hl
  exact hl

end SpinGlass
