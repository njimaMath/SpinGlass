import SpinGlass.Parisi.Coupled.Derivative.First

/-! Coordinatewise transport of cascade tilts for coupled marks. -/

open MeasureTheory ProbabilityTheory Finset Set Filter Topology
open scoped ENNReal NNReal BigOperators

/-!
### Coordinatewise transport of cascade tilts

The proof of Proposition 14.6.4(a), equation (14.177), compares two descriptions of the same
coupled cascade.
The Gaussian marks used by `pairSiteY₀` are functions `Fin 2 → ℝ`; the square appearing in
Talagrand's formula is expressed using pairs `ℝ × ℝ`.  We first prove that `cascadeTilt` is
unchanged when every mark law and every observable are transported by measurable maps.  We
then apply this fact to `MeasurableEquiv.finTwoArrow` and to the level-dependent coupling maps.
-/

namespace ProbabilityTheory

universe u v

noncomputable section

/-- Push each mark law forward by the map assigned to that coordinate.

The measurability proof is retained as an argument so that the probability-measure instance for
the pushforward family can be synthesized without introducing a separate local instance at each
use site. -/
def coordinateMapLaw
    {T : Type u} {T' : Type v}
    [MeasurableSpace T] [MeasurableSpace T']
    {k : ℕ}
    (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)]
    (φ : Fin k → T → T')
    (_hφ : ∀ i, Measurable (φ i))
    (i : Fin k) : Measure T' :=
  (μs i).map (φ i)

/-- Coordinatewise pushforwards of probability laws are probability laws. -/
instance coordinateMapLaw_isProbabilityMeasure
    {T : Type u} {T' : Type v}
    [MeasurableSpace T] [MeasurableSpace T']
    {k : ℕ}
    (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)]
    (φ : Fin k → T → T')
    (hφ : ∀ i, Measurable (φ i))
    (i : Fin k) :
    IsProbabilityMeasure (coordinateMapLaw μs φ hφ i) := by
  unfold coordinateMapLaw
  exact Measure.isProbabilityMeasure_map (hφ i).aemeasurable

/-- Applying the coordinate maps after `Fin.cons` agrees with mapping the head and tail
separately. -/
private lemma coordinateMap_cons
    {T : Type u} {T' : Type v}
    {k : ℕ}
    (φ : Fin (k + 1) → T → T')
    (z : T) (ys : Fin k → T) :
    (fun i => φ i ((Fin.cons z ys : Fin (k + 1) → T) i))
      =
    Fin.cons (φ 0 z) (fun i => φ i.succ (ys i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

/-- The first cascade weight commutes with coordinatewise transport.

The denominator follows from `cascadeRec_map` on all coordinates.  The numerator follows from
the same theorem on the tail coordinates, after rewriting the mapped `Fin.cons`. -/
private lemma cascadeW_coordinateMap
    {T : Type u} {T' : Type v}
    [MeasurableSpace T] [MeasurableSpace T']
    {k : ℕ}
    (ms : Fin (k + 1) → ℝ)
    (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)]
    (φ : Fin (k + 1) → T → T')
    (hφ : ∀ i, Measurable (φ i))
    {G : (Fin (k + 1) → T') → ℝ≥0∞}
    (hG : Measurable G)
    (z : T) :
    cascadeW k ms (coordinateMapLaw μs φ hφ) G (φ 0 z)
      =
    cascadeW k ms μs
      (fun zs => G (fun i => φ i (zs i))) z := by
  have hden :
      cascadeRec (k + 1) ms (coordinateMapLaw μs φ hφ) G
        =
      cascadeRec (k + 1) ms μs
        (fun zs => G (fun i => φ i (zs i))) := by
    change cascadeRec (k + 1) ms
      (fun i => (μs i).map (φ i)) G = _
    exact cascadeRec_map (T := T) (T' := T') (k + 1)
      ms μs φ hφ hG
  have hGz :
      Measurable fun ys : Fin k → T' => G (Fin.cons (φ 0 z) ys) :=
    hG.comp
      (measurable_fin_cons.comp
        (measurable_const.prodMk measurable_id))
  have hnum :
      cascadeRec k (Fin.tail ms)
          (Fin.tail (coordinateMapLaw μs φ hφ))
          (fun ys => G (Fin.cons (φ 0 z) ys))
        =
      cascadeRec k (Fin.tail ms) (Fin.tail μs)
          (fun ys => G (fun i =>
            φ i ((Fin.cons z ys : Fin (k + 1) → T) i))) := by
    change cascadeRec k (Fin.tail ms)
      (fun i => ((Fin.tail μs) i).map ((Fin.tail φ) i))
      (fun ys => G (Fin.cons (φ 0 z) ys)) = _
    have h := cascadeRec_map (T := T) (T' := T') k
      (Fin.tail ms) (Fin.tail μs) (Fin.tail φ)
      (fun i => hφ i.succ) hGz
    simpa only [Fin.tail, coordinateMap_cons] using h
  unfold cascadeW
  rw [hnum, hden]

/-- A cascade tilt computed with pushed-forward mark laws equals the original tilt applied to
the pulled-back weight and observable. -/
theorem cascadeTilt_coordinateMap
    {T : Type u} {T' : Type v}
    [MeasurableSpace T] [MeasurableSpace T']
    (k : ℕ) :
    ∀ (ms : Fin k → ℝ)
      (μs : Fin k → Measure T)
      [∀ i, IsProbabilityMeasure (μs i)]
      (φ : Fin k → T → T')
      (hφ : ∀ i, Measurable (φ i))
      {G A : (Fin k → T') → ℝ≥0∞},
      Measurable G → Measurable A →
      cascadeTilt k ms (coordinateMapLaw μs φ hφ) G A
        =
      cascadeTilt k ms μs
        (fun zs => G (fun i => φ i (zs i)))
        (fun zs => A (fun i => φ i (zs i))) := by
  induction k with
  | zero =>
      intro ms μs _ φ hφ G A hG hA
      rw [cascadeTilt_zero, cascadeTilt_zero]
      exact congrArg A (Subsingleton.elim _ _)
  | succ k ih =>
      intro ms μs _ φ hφ G A hG hA
      rw [cascadeTilt_succ, cascadeTilt_succ]
      -- This is the integrand required by `lintegral_map` at the first level.
      have hM :
          Measurable fun z : T' =>
            cascadeW k ms (coordinateMapLaw μs φ hφ) G z *
            cascadeTilt k (Fin.tail ms)
              (Fin.tail (coordinateMapLaw μs φ hφ))
              (fun ys => G (Fin.cons z ys))
              (fun ys => A (Fin.cons z ys)) := by
        exact
          (measurable_cascadeW k ms
            (coordinateMapLaw μs φ hφ) hG).mul
          (measurable_cascadeTilt_prod k
            (Fin.tail ms)
            (Fin.tail (coordinateMapLaw μs φ hφ))
            (Gs := fun z ys => G (Fin.cons z ys))
            (As := fun z ys => A (Fin.cons z ys))
            (hG.comp measurable_fin_cons)
            (hA.comp measurable_fin_cons))
      change (∫⁻ z,
        cascadeW k ms (coordinateMapLaw μs φ hφ) G z *
          cascadeTilt k (Fin.tail ms)
            (Fin.tail (coordinateMapLaw μs φ hφ))
            (fun ys => G (Fin.cons z ys))
            (fun ys => A (Fin.cons z ys))
        ∂(μs 0).map (φ 0)) = _
      rw [lintegral_map hM (hφ 0)]
      refine lintegral_congr fun z => ?_
      rw [cascadeW_coordinateMap ms μs φ hφ hG z]
      -- The remaining coordinates are transported by the tail of `φ`.
      have hinner := ih
        (Fin.tail ms) (Fin.tail μs) (Fin.tail φ)
        (fun i => hφ i.succ)
        (G := fun ys => G (Fin.cons (φ 0 z) ys))
        (A := fun ys => A (Fin.cons (φ 0 z) ys))
        (hG.comp
          (measurable_fin_cons.comp
            (measurable_const.prodMk measurable_id)))
        (hA.comp
          (measurable_fin_cons.comp
            (measurable_const.prodMk measurable_id)))
      let _ : ∀ i, IsProbabilityMeasure
          (coordinateMapLaw (Fin.tail μs) (Fin.tail φ)
            (fun i => hφ i.succ) i) :=
        fun i => coordinateMapLaw_isProbabilityMeasure
          (Fin.tail μs) (Fin.tail φ) (fun i => hφ i.succ) i
      change _ * cascadeTilt k (Fin.tail ms)
        (coordinateMapLaw (Fin.tail μs) (Fin.tail φ)
          (fun i => hφ i.succ))
        (fun ys => G (Fin.cons (φ 0 z) ys))
        (fun ys => A (Fin.cons (φ 0 z) ys)) = _
      rw [hinner]
      simp only [Fin.tail, coordinateMap_cons]

/-- Pulling the paired cascade back through `couplingMap` turns the product observable into the
tilted conditional square.

The proof first transports independent raw pairs to `pairMarkLaw`, then uses
`cascadeTiltPair_eq_cascadeTilt` and Talagrand's product identity `cascadeTiltPair_prod`. -/
theorem cascadeTilt_coupling_prod
    {T : Type u}
    [MeasurableSpace T]
    (k r : ℕ)
    (ms : Fin k → ℝ)
    (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)]
    {G A : (Fin k → T) → ℝ≥0∞}
    (hG : Measurable G)
    (hA : Measurable A)
    (hGpos : ∀ zs, 0 < G zs)
    (hpos : ∀ i, 0 < ms i) :
    cascadeTilt k
        (halveBelow r ms)
        (fun p => (μs p).prod (μs p))
        (fun zs =>
          G (fun i => (couplingMap r i (zs i)).1)
            *
          G (fun i => (couplingMap r i (zs i)).2))
        (fun zs =>
          A (fun i => (couplingMap r i (zs i)).1)
            *
          A (fun i => (couplingMap r i (zs i)).2))
      =
    cascadeTiltSq k r ms μs G A := by
  set G₂ : (Fin k → T × T) → ℝ≥0∞ :=
    fun zs =>
      G (fun i => (zs i).1) *
      G (fun i => (zs i).2)
  set A₂ : (Fin k → T × T) → ℝ≥0∞ :=
    fun zs =>
      A (fun i => (zs i).1) *
      A (fun i => (zs i).2)
  have hG₂ : Measurable G₂ := by
    dsimp [G₂]
    exact (hG.comp measurable_pairFst).mul (hG.comp measurable_pairSnd)
  have hA₂ : Measurable A₂ := by
    dsimp [A₂]
    exact (hA.comp measurable_pairFst).mul (hA.comp measurable_pairSnd)
  let μprod : Fin k → Measure (T × T) :=
    fun p => (μs p).prod (μs p)
  let φ : Fin k → (T × T) → (T × T) :=
    fun p => couplingMap r p
  have hφ : ∀ i, Measurable (φ i) :=
    fun i => measurable_couplingMap r i
  have hmap :
      coordinateMapLaw μprod φ hφ
        =
      pairMarkLaw r μs := by
    funext p
    change
      ((μs p).prod (μs p)).map (couplingMap r p)
        =
      pairMarkLaw r μs p
    exact congrFun
      (map_couplingMap_prod_eq_pairMarkLaw r μs) p
  calc
    cascadeTilt k
        (halveBelow r ms)
        (fun p => (μs p).prod (μs p))
        (fun zs =>
          G (fun i => (couplingMap r i (zs i)).1)
            *
          G (fun i => (couplingMap r i (zs i)).2))
        (fun zs =>
          A (fun i => (couplingMap r i (zs i)).1)
            *
          A (fun i => (couplingMap r i (zs i)).2))
        =
      cascadeTilt k
        (halveBelow r ms)
        (coordinateMapLaw μprod φ hφ)
        G₂ A₂ := by
          symm
          simpa [μprod, φ, G₂, A₂] using
            (cascadeTilt_coordinateMap
              (T := T × T) (T' := T × T) k
              (halveBelow r ms)
              μprod φ hφ hG₂ hA₂)
    _ =
      cascadeTilt k
        (halveBelow r ms)
        (pairMarkLaw r μs)
        G₂ A₂ := by
          exact cascadeTilt_congr_measure
            (halveBelow r ms) hmap G₂ A₂
    _ =
      cascadeTiltPair k r ms μs G A₂ := by
          symm
          exact cascadeTiltPair_eq_cascadeTilt
            k r ms μs hG hA₂ hGpos hpos
    _ =
      cascadeTiltSq k r ms μs G A := by
          exact cascadeTiltPair_prod
            k r ms μs hG hA

end

end ProbabilityTheory
