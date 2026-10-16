import SpinGlass.Parisi.Coupled.CoupledFreeTrialWitness
import SpinGlass.Parisi.Coupled.CoupledRootTrialComparison
import SpinGlass.Parisi.Coupled.CoupledRootSignedTrialComparison
import SpinGlass.Parisi.Coupled.CoupledMainOutsideCompact

/-!
# Continuous physical witnesses for the full main estimate

Canonical, free inner, free outer and positive root trials all bound
the original constrained pressure with the Gaussian trial held fixed.
They supply a common continuous scalar interface for the compact cover
following Propositions 14.8.6 and 14.8.7.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

inductive ParisiMainTrial {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) where
  | canonical (w : ParisiCanonicalTrial qs)
  | inner (p : Fin k) (level_eq : p.succ = r) (w : ParisiInnerFreeTrial ms qs p)
  | outer (w : ParisiOuterFreeTrial ms qs r)
  | root (level_eq : r = 0) (v : ℝ) (hv : v ∈ Icc (0 : ℝ) (qs 0))
      (m : ℝ) (hm : m ∈ Ioc (0 : ℝ) (mExt ms 1)) (lam : ℝ)
  | signedRoot (level_eq : r = 0) (v : ℝ) (hv : v ∈ Icc (-(qs 0)) (0 : ℝ))
      (m : ℝ) (hm : m ∈ Ioc (0 : ℝ) (mExt ms 1)) (lam : ℝ)

noncomputable def parisiMainTrialGap (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (w : ParisiMainTrial ms qs r) (t u : ℝ) : ℝ :=
  match w with
  | .canonical w => parisiCanonicalTrialGap μh ξ ms qs w.negative r w.split w.magnitude w.coupling t u
  | .inner p _ w => parisiInnerFreeTrialGap μh ξ ms qs p w.overlap w.mass w.coupling t u
  | .outer w => parisiOuterFreeTrialGap μh ξ ms qs r w.overlap w.mass w.coupling t u
  | .root _ v _ m _ lam => parisiRootTrialGap μh ξ ms qs v m lam t u
  | .signedRoot _ v _ m _ lam => parisiRootSignedTrialGap μh ξ ms qs v m lam t u

/-- The concrete response witnesses cover both signs of the initial interval.
The two response hypotheses are the scalar inputs to this bridge. -/
theorem exists_parisiMainTrial_positive_root_gap_of_response
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : |u| ≤ qs 0)
    (hpositive : u ∈ Icc (0 : ℝ) (qs 0) → parisiRootResponseGap μh ξ ms qs t u ≠ 0)
    (hnegative : u ∈ Icc (-(qs 0)) (0 : ℝ) →
      parisiRootSignedResponseGap μh ξ ms qs t u ≠ 0) :
    ∃ w : ParisiMainTrial ms qs 0, 0 < parisiMainTrialGap μh ξ ms qs 0 w t u := by
  rcases le_total 0 u with hu0 | hu0
  · have huP : u ∈ Icc (0 : ℝ) (qs 0) := ⟨hu0, (le_abs_self u).trans hu⟩
    obtain ⟨m, hmass, lam, hg⟩ := exists_parisiRootTrialGap_pos_of_response_ne_zero
      hμ hξ ms qs hm hq ht huP (hpositive huP)
    exact ⟨.root rfl u huP m hmass lam, hg⟩
  · have huS : u ∈ Icc (-(qs 0)) (0 : ℝ) := ⟨(abs_le.1 hu).1, hu0⟩
    obtain ⟨m, hmass, lam, hg⟩ := exists_parisiRootSignedTrialGap_pos_of_response_ne_zero
      hμ hξ ms qs hm hq ht huS (hnegative huS)
    exact ⟨.signedRoot rfl u huS m hmass lam, hg⟩

/-- All actual fixed-trial gaps are continuous on the whole time and
realized-overlap plane. Only the field law's first moment is needed. -/
theorem continuous_parisiMainTrialGap_time_overlap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) (r : Fin (k + 1)) (w : ParisiMainTrial ms qs r) :
    Continuous (fun x : ℝ × ℝ => parisiMainTrialGap μh ξ ms qs r w x.1 x.2) := by
  cases w with
  | canonical w =>
    exact continuous_parisiCanonicalTrialGap_time_overlap hμ hξ ms qs w.negative r w.split
      (w.magnitude_mem_Icc hq) w.coupling
  | inner p hp w =>
    exact continuous_parisiInnerFreeTrialGap_time_overlap hμ hξ ms qs p hm (w.mass_pos hm)
      w.overlap w.coupling
  | outer w =>
    exact continuous_parisiOuterFreeTrialGap_time_overlap hμ hξ ms qs r hm w.mass_pos w.overlap w.coupling
  | root hr v hv m hmass lam =>
    exact continuous_parisiRootTrialGap_time_overlap hμ hξ ms qs hm hmass.1 v lam
  | signedRoot hr v hv m hmass lam =>
    exact continuous_parisiRootSignedTrialGap_time_overlap hμ hξ ms qs hm hmass.1
      (hmass.2.trans (mExt_le_one (fun i => (hm.2.2 i).le) _)) v lam

/-- Every witness bounds the original pressure at every realizable
constraint. Its choice therefore precedes volume and Gaussian realization. -/
theorem randomFieldParisiAuxPairPressure_le_mainTrialGap {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) (r : Fin (k + 1)) (w : ParisiMainTrial ms qs r)
    {t : ℝ} (u : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t u G₀ ≤
      2 * parisiInterpolationBracket μh ξ ms qs t - parisiMainTrialGap μh ξ ms qs r w t u := by
  cases w with
  | canonical w =>
    exact randomFieldParisiAuxPairPressure_le_canonicalTrialGap hμ hN hξ ms qs hm hq
      w.negative r w.split u ht w.admissible w.coupling G₀ hreach
  | inner p hp w =>
    subst r
    simpa only [parisiMainTrialGap, Fin.val_succ, Nat.add_assoc] using
      randomFieldParisiAuxPairPressure_le_innerFreeTrialGap hμ hN hξ ms qs p hm hq u ht w.overlap_mem
        w.mass_mem.1 w.mass_mem.2 w.coupling G₀ hreach
  | outer w =>
    exact randomFieldParisiAuxPairPressure_le_outerFreeTrialGap hμ hN hξ ms qs r hm hq u ht w.overlap_mem
      w.mass_pos w.mass_mem.1 w.mass_mem.2 w.coupling G₀ hreach
  | root hr v hv m hmass lam =>
    subst r
    exact randomFieldParisiAuxPairPressure_le_rootTrialGap hμ hN hξ ms qs hm hq u ht hv
      hmass.1 hmass.2 lam G₀ hreach
  | signedRoot hr v hv m hmass lam =>
    subst r
    exact randomFieldParisiAuxPairPressure_le_rootSignedTrialGap hμ hN hξ ms qs hm hq u ht hv
      hmass.1 hmass.2 lam G₀ hreach

end SpinGlass
