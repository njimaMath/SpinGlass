# ARCHITECTURE.md

## Purpose of this document

This document describes the **current repository state and dependency architecture specifically for the Parisi lower bound** in `njimaMath/SpinGlass`, with Talagrand Vol. II Chapter 14 as the reference proof.

It is meant to answer four questions for an implementation agent:

- What is already proved?
- What is still missing?
- Which files own which mathematical abstractions?
- In what dependency order must the remaining lower-bound proof be built?

The target route is Talagrand §§14.5–14.10, not the alternative Chapter 15 route.

---

## Repository / toolchain baseline

At the inspected baseline:

```text
repository: njimaMath/SpinGlass
branch:     main
Lean:       leanprover/lean4:v4.34.0-rc2
mathlib:    v4.34.0-rc2
```

`lakefile.toml` defines two Lean libraries:

```text
Common    -- Mathlib gaps and general-purpose probability/analysis infrastructure
SpinGlass -- Talagrand/spin-glass formalization
```

There is also a dependency on `matteo-ax/GibbsMeasure` for exchangeability/de Finetti machinery used in the limit layer. The Chapter 14 lower-bound route itself should not need the Chapter 15 exchangeability/ultrametricity stack.

CI currently runs `lake build` on changes to Lean/toolchain files.

### Important CI coverage issue

The inspected `SpinGlass.lean` imports a large fraction of the repository, including the Chapter 14 upper-bound/coupled infrastructure, but **does not import `SpinGlass.Parisi.ParisiLowerBound`**. Therefore a green default build does not automatically certify the current lower-bound capstone file.

During implementation, compile the leaf explicitly. Once the proof is finished, import it from `SpinGlass.lean`.

---

## Mathematical target

Talagrand states the Parisi formula under condition (14.101), then separates the proof into the nonzero-field theorem (14.5.2) and a field-to-zero reduction (14.5.1). In the book, `h ≠ 0` means positive second moment for the random field. The proof first constructs MIN parameters, proves a coupled-copy main estimate, localizes the overlap, derives convergence of the interpolation for every `t₀<1`, and finally passes to `t=1` using the coarse derivative bound (14.109).

In the repository this is represented by the theorem:

```lean
eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy_of_nondegenerate
```

in `SpinGlass/Parisi/ParisiLowerBound.lean`.

Its assumptions are:

```text
μh is a probability law
NondegenerateExternalFieldLaw μh
TalagrandXiCondition ξ
∀ N, overlapCovMatrix N ξ is positive semidefinite
```

and its conclusion is the eventual epsilon form of the lower bound:

```text
randomFieldParisiInf μh ξ - ε ≤ iidFieldMixedPSpinFreeEnergy N μh ξ.
```

At the inspected baseline this theorem is the major proof hole.

---

## Top-level dependency map

```text
TalagrandXiCondition / model covariance / i.i.d. site field
        │
        ├─────────────── upper-bound branch ───────────────────────┐
        │                                                         │
        │   Parisi functional / cascade recursion                 │
        │        │                                                │
        │        ├─ GuerraFixedWeights                            │
        │        ├─ GuerraParisi                                  │
        │        └─ ParisiInf ── finite-volume Guerra upper bound │
        │                                                         │
        └─────────────── lower-bound branch ───────────────────────┤
                  │                                               │
                  ├─ ParisiMin (partial MIN only)                 │
                  │      │                                        │
                  │      └─ [missing: compact minimization +      │
                  │          redundant-level removal]             │
                  │                                               │
                  ├─ ParisiQDeriv ── q-stationarity / 14.7.5      │
                  │      │                                        │
                  │      └─ [missing: mass/split variation,       │
                  │          U/f estimates, 14.283]               │
                  │                                               │
                  ├─ Coupled* stack ── §14.6 complete core        │
                  │      │                                        │
                  │      └─ [missing: random-field adapters +     │
                  │          exact main-estimate witnesses]       │
                  │                                               │
                  ├─ [missing: Theorem 14.5.7 main estimate]      │
                  │                                               │
                  ├─ [missing: Prop. 14.5.8 concentration]        │
                  │                                               │
                  ├─ [missing: Prop. 14.5.6 localization]         │
                  │                                               │
                  ├─ [missing: Theorem 14.5.4 interpolation]      │
                  │                                               │
                  └─ ParisiLowerBound                             │
                         │                                        │
                         ├─ nondegenerate theorem  [SORRY]         │
                         ├─ zero-second-moment reduction [proved]  │
                         ├─ convergence squeeze [proved modulo gap]│
                         └─ liminf corollary [proved modulo gap] ──┘
```

---

## External-field architecture

### Law-level semantics

`SpinGlass/Parisi/README.md` documents the current field model:

```text
μh : Measure ℝ                     -- one-site field law
externalFieldVecLaw N μh           -- i.i.d. field vector on Fin N
sharedReplicaSiteField hVec        -- same realized field used by both replicas
```

This matches Talagrand (14.65), where `(h_i)` are i.i.d. copies of a random variable h.

### Separation of conditional and averaged statements

A central architectural choice is that branch Hamiltonians, site factorization, cascade endpoints, pair Gibbs averages, and Guerra interpolation often accept a **realized vector**

```lean
h : Fin N → ℝ
```

and are proved conditionally on that vector. Law-level free energies/functionals are then obtained by integration against `externalFieldVecLaw N μh`.

This is exactly the right architecture for the lower bound because Proposition 14.5.8 needs Gaussian concentration while the final field assumption is only finite second moment. Conditioning on `hVec` leaves a purely Gaussian concentration problem with `hVec` as an affine shift.

### Nondegenerate vs zero field

`NondegenerateExternalFieldLaw μh` is the positive-second-moment branch.

`ParisiLowerBound.lean` already proves the zero-second-moment case from:

- `externalFieldLaw_eq_dirac_zero_of_second_moment_eq_zero`,
- field continuity of the finite-volume free energy,
- field continuity of the Parisi infimum,
- Dirac compatibility theorems.

This reduction should remain downstream of the nondegenerate theorem.

---

## Covariance-profile architecture

### `TalagrandXiCondition`

Defined in `ParisiQDeriv.lean`. It packages the analytic content of Talagrand (14.101) in the repository's current form:

```text
ξ even
ξ convex on ℝ
ξ' continuous on [0,1]
ξ differentiable on [0,1]
ξ' differentiable on [0,1]
ξ''(x) > 0 for x ≠ 0 in [0,1]
ξ'' differentiable on (0,1]
ξ'''(x) ≥ 0 on (0,1]
```

The code derives, among other things, strict monotonicity of `deriv ξ` on the physical interval.

### PSD is separate

The capstone also assumes:

```lean
∀ N, (overlapCovMatrix N ξ).PosSemidef
```

This is **not** encoded as a consequence of `TalagrandXiCondition`; it is the realizability condition for the Gaussian Hamiltonian and must stay explicit.

---

## Functional / upper-bound layer — already in place

### `SpinGlass/Parisi/RandomFieldFunctional.lean`

Owns the random-field version of the one-site Parisi recursion and functional.

Key conceptual outputs:

```text
randomFieldParisiX₀
randomFieldParisiFunctional
randomFieldParisiFunctional_eq_integral
```

Constant fields are recovered by `Measure.dirac` simplification theorems.

### `SpinGlass/Parisi/GuerraParisi.lean`

Implements Guerra's broken replica-symmetry bound (Talagrand Theorem 14.4.3).

The file-level documentation records:

- endpoint evaluation using the cascade recursion,
- pair-average identity from the Poisson–Dirichlet cascade,
- Abel summation to the Parisi functional,
- extension from strict to nondecreasing positive masses by continuity.

### `SpinGlass/Parisi/ParisiInf.lean`

Defines:

```text
randomFieldParisiSet μh ξ
randomFieldParisiInf μh ξ
```

and proves the finite-volume optimized Guerra bound:

```lean
iidFieldMixedPSpinFreeEnergy_le_randomFieldParisiInf
```

under its explicit differentiability assumptions.

This is the **upper** half of the Parisi formula and will later provide the squeeze once the lower half is complete.

Important architectural fact: the lower-bound target should not be proved by manipulating `sInf` alone; Talagrand needs a finite-dimensional near-minimizer with exact coordinate minimality.

---

## MIN layer — partially complete

### `SpinGlass/Parisi/ParisiMin.lean`

What exists:

- monotonicity of `parisiTheta` on `[0,1]`;
- a uniform lower bound for admissible random-field functional values;
- `BddBelow (randomFieldParisiSet μh ξ)` under `TalagrandXiCondition`;
- `exists_randomFieldParisiFunctional_lt_inf_add`;
- `exists_randomFieldParisiFunctional_lt_inf_add_of_talagrand`.

The last theorem selects strict masses and monotone q-values with functional value within positive tolerance of the global infimum.

The closed-overlap portion is also available through:

- `continuousOn_randomFieldParisiFunctional_overlapCube`;
- `exists_randomFieldParisiQMinimum_of_fixed_masses`;
- `randomFieldParisiFunctional_erase_adjacent_eq`;
- `exists_nearOptimal_randomFieldParisiQMinimizer`.

These establish joint overlap continuity, closed overlap minimization for fixed masses, and deletion of repeated overlaps without changing the functional. Fixed-q mass continuity is available in `continuousOn_parisiFunctional`.

### What is missing for Talagrand MIN

Talagrand Definition 14.5.3 requires both:

```text
P_k(m,q) ≤ P + ε             (14.105)
P_k(m,q) is a true fixed-k minimum  (14.106)
```

The current theorem provides only the near-infimum part.

The remaining implementation is:

```text
joint mass/overlap continuity on the closed mass domain, including exponent zero
        ↓
mass minimization
        ↓
equal-mass and endpoint-mass reduction
        ↓
strict MIN parameters preserving the minimum value
```

A minimum over overlaps alone is not full MIN. The completed overlap-level reduction is implemented in `ParisiParameterContinuity.lean`, `ParisiLevelReduction.lean`, and `ParisiCompactMin.lean`; the remaining mass-coordinate work is the first hard dependency of the lower-bound route.

---

## q-variation layer — substantially complete

### `SpinGlass/Parisi/ParisiQDeriv.lean`

This file is more advanced than some older README text suggests.

It defines:

```text
ParisiMAdmissible
ParisiQAdmissible
IsParisiQMinimizer
IsRandomFieldParisiQMinimizer
qUpdate
randomFieldParisiQMoment
```

and develops the Cole–Hopf spatial/variance derivative calculus needed for q-coordinate differentiation.

Most importantly, it already contains a concrete random-field version of Proposition 14.7.5:

```lean
randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
```

For a nondegenerate probability law and a q-minimizer it gives:

```text
strict q-chain including endpoints
q_r = corresponding recursion moment
```

which is the analogue of Talagrand (14.221)–(14.222).

The corresponding i.i.d.-field theorem is `iidExternalFieldParisiQ_strict_chain_and_eq_moment_of_isMin`, and `exists_nearOptimal_randomFieldParisi_stationary` supplies near-optimal overlap minimizers with concrete stationarity moments.

### Missing part of §14.7

The main estimate needs much more than q-stationarity. Missing are the mass/splitting variations and their quantitative consequences:

```text
Φ(m,u)
U(v)
f(u)
(14.239)
U'' < 0
U'(0) = q_r
f(q_r)=f'(q_r)=0
f(q_{r-1})=0 for r≥2
uniform derivative bounds
f(u) ≥ -M√ε
q₁ ≥ 1/M
curvature estimate (14.283)
```

These should be layered on top of `ParisiQDeriv`, not rebuilt independently.

---

## Coupled-copy / §14.6 architecture — core is already strong

The repository has a substantial two-replica stack.

### Generic tree / interpolation layers

Relevant modules include:

```text
TreeCov
TreeField
TreeFieldLaw
SiteTreeFieldLaw
TreeTrace
PairTreeField
PairTreeFieldIndep
PairLevels
CoupledTrace
CoupledScheme
CoupledInterpolation
CoupledLevels
CoupledBoundLaw
CoupledFixedWeights
BranchAverages
BranchLimit
LevelBoundLaw
```

These files encode the tree/cascade branch conventions, truncation, endpoint factorization, and fixed-weight/law limits.

### `CoupledProp.lean`

Implements Talagrand Proposition 14.6.3 for the canonical coupling.

Key definitions/results include:

```text
couplingFactorSgn
couplingRhoSgn
coupled_bound_coupling
coupled_bound_coupling_zero
coupled_bound_coupling_of_top
```

The sign `η = ±1` is explicit, which is important for negative-overlap cases.

### `CoupledLambdaZero.lean`

Implements the λ=0 identification:

```text
Y₀(0) = 2 X₀
```

and the fact that the specialized RHS equals twice the Parisi functional.

This is the baseline equality from which the main estimate obtains an improvement.

### `CoupledDeriv.lean`

Implements the first λ derivative of `Y₀` and the uniform bound:

```text
|Y₀'(λ)| ≤ 1.
```

### `CoupledSecondDeriv.lean`

Implements Talagrand's Lemma 14.6.5 in the useful second-derivative form:

```text
0 ≤ Y₀''(λ) ≤ 1
```

and therefore the tangent/quadratic upper bound used by the main estimate:

```text
Y₀(λ) ≤ Y₀(0) + λ Y₀'(0) + λ²/2.
```

### Remaining coupled work

The gap is no longer “prove Proposition 14.6.3”. It is:

- integrable adapters from the realized shared site field to law-level i.i.d. field statements;
- exact canonical parameter witnesses used in the seven main-estimate cases;
- possibly specialized slope-at-zero identifications in the exact `U/f` notation used by the variational layer.

The relevant conditional interfaces include `coupled_bound_coupling_siteField`, `coupled_bound_coupling_zero_siteField`, and `coupled_bound`. The law-level adapters must preserve the shared external-field vector between replicas.

---

## Main estimate — missing

Talagrand Theorem 14.5.7 states a uniform quadratic penalty:

```text
Ψ_r(t,u) ≤ 2 ψ(t) - (u-q_r)^2 / K
```

for `t≤t₀`, with K independent of `u,t,N` after MIN parameters are fixed.

Talagrand proves it through seven cases, Propositions 14.8.1–14.8.7:

```text
14.8.1  left-near q_r
14.8.2  left-far, r≥2
14.8.3  r=1 special / |u|≤q₁
14.8.4  right-near
14.8.5  right-far
14.8.6  outside neighboring q interval, t>0
14.8.7  t=0, u≠q_r
```

The uniform strict improvement and seven-case assembly remain missing; the lambda Taylor bound alone is insufficient.

The recommended architecture is a dedicated `ParisiMainEstimate.lean` that depends only on:

```text
MIN package
§14.7 variational package
CoupledProp / LambdaZero / Deriv / SecondDeriv
basic compactness/scalar calculus
```

It should not depend on finite-volume concentration or localization.

---

## Proposition 14.5.8 concentration — missing

Talagrand's Proposition 14.5.8 converts a strict constrained-pressure gap into exponentially small Gibbs mass at the exact overlap value.

The book's proof uses:

```text
J_p(u), J_p recursion
V_p multiplicative weights
endpoint factor B ≤ 1
expectation gap
Gaussian concentration of log E₁(V₁...V_k B)
```

The repository has the generic ingredients, but not this exact bridge theorem.

### Dependency recommendation

Create a layer after `ParisiMainEstimate` but before localization:

```text
ParisiConcentration.lean
```

It should depend on:

- finite Gibbs/cascade recursion;
- Gaussian-field realization/concentration;
- external field only through conditioning on a realized vector.

It should **not** depend on Theorem 14.5.7; Proposition 14.5.8 is logically independent and consumes only a generic strict gap assumption.

---

## Proposition 14.5.6 localization — missing

This layer combines:

```text
main estimate (14.112)
+
Proposition 14.5.8 exponential exact-overlap bound
+
finite overlap range |{n/N}| ≤ 2N+1
```

and proves that conditioned on cascade branches meeting at level r, the spin overlap is close to `q_r`.

The current generic pair-Gibbs integration identities already exist (`gibbsPair`, `integral_gibbsPair_eq`, `integral_pairAvg` according to the gap map).

Recommended dedicated file:

```text
ParisiLocalization.lean
```

---

## Theorem 14.5.4 interpolation lower comparison — missing

This is the decisive bridge from overlap localization back to the one-replica free energy.

Talagrand uses the exact derivative remainder:

```text
ξ(R₁₂) - R₁₂ ξ'(q_r) + θ(q_r)
```

and the local quadratic bound:

```text
|remainder| ≤ K (R₁₂-q_r)^2.
```

Localization then gives:

```text
(ψ-φ)' ≤ K (ψ-φ+ε₁).
```

Together with equality at `t=0`, a differential inequality yields convergence for each fixed `t≤t₀<1`.

The repository already has Guerra interpolation and derivative infrastructure, but the reverse/localization-based inequality is not present.

Recommended dedicated file:

```text
ParisiInterpolationLower.lean
```

This file should depend on `ParisiLocalization` and existing Guerra interpolation, but not on the final `ParisiLowerBound` assembly.

---

## Endpoint / final assembly

Talagrand then uses the coarse derivative bound (14.109):

```text
ψ'(t)-M ≤ φ'(t) ≤ ψ'(t)
```

and sends `t₀↑1`.

At the repository level the final nondegenerate theorem should become a short proof:

```text
choose t₀ close to 1
choose MIN(ε_MIN)
apply Theorem 14.5.4 at t₀
use endpoint derivative comparison
identify φ(1) with finite-volume free energy
identify ψ(1) with chosen Parisi functional
use randomFieldParisiInf ≤ chosen functional
finish epsilon bookkeeping
```

After this, the rest of `ParisiLowerBound.lean` is already structurally complete:

### General finite-second-moment theorem

Branches on whether the second moment is positive.

Positive branch: new nondegenerate theorem.

Zero branch: identifies the law with `dirac 0`, perturbs to a small constant nonzero field, applies the nondegenerate theorem, and removes the perturbation by field continuity.

### Convergence theorem

Combines:

```text
lower eventual inequality
+
finite-volume optimized Guerra upper bound
```

using `tendsto_order`.

### Liminf theorem

Immediate from convergence.

---

## Current file inventory relevant to the lower bound

### Capstone / status

```text
SpinGlass/Parisi/ParisiLowerBound.lean
SpinGlass/Parisi/README.md
README.md
```

### Functional / upper bound

```text
SpinGlass/Parisi/RandomExternalField.lean
SpinGlass/Parisi/RandomFieldFunctional.lean
SpinGlass/Parisi/GuerraBound.lean
SpinGlass/Parisi/GuerraFixedWeights.lean
SpinGlass/Parisi/GuerraParisi.lean
SpinGlass/Parisi/ParisiInf.lean
```

### MIN / variational

```text
SpinGlass/Parisi/ParisiMin.lean
SpinGlass/Parisi/ParisiQDeriv.lean
```

### Coupled copies

```text
SpinGlass/Parisi/CoupledTrace.lean
SpinGlass/Parisi/CoupledScheme.lean
SpinGlass/Parisi/CoupledEndpoint.lean
SpinGlass/Parisi/CoupledBranch.lean
SpinGlass/Parisi/CoupledInterpolation.lean
SpinGlass/Parisi/CoupledLevels.lean
SpinGlass/Parisi/CoupledBoundLaw.lean
SpinGlass/Parisi/CoupledFixedWeights.lean
SpinGlass/Parisi/CoupledParisi.lean
SpinGlass/Parisi/CoupledSite.lean
SpinGlass/Parisi/CoupledProp.lean
SpinGlass/Parisi/CoupledLambdaZero.lean
SpinGlass/Parisi/CoupledDeriv.lean
SpinGlass/Parisi/CoupledSecondDeriv.lean
SpinGlass/Parisi/PairLevels.lean
```

### Tree/cascade limits

```text
SpinGlass/Parisi/TreeCov.lean
SpinGlass/Parisi/TreeField.lean
SpinGlass/Parisi/TreeFieldLaw.lean
SpinGlass/Parisi/SiteTreeFieldLaw.lean
SpinGlass/Parisi/TreeTrace.lean
SpinGlass/Parisi/BranchAverages.lean
SpinGlass/Parisi/BranchLimit.lean
SpinGlass/Parisi/LevelBoundLaw.lean
```

### Continuity / zero field

```text
SpinGlass/Parisi/ExternalFieldZero.lean
SpinGlass/Parisi/FieldContinuity.lean
```

### General concentration / Gibbs infrastructure likely reusable

```text
SpinGlass/Poincare.lean
SpinGlass/GaussFieldFluctuation.lean
SpinGlass/FiniteGibbs/*
Common/Mathlib/Probability/Distributions/Gaussian/*
```

---

## Recommended new dependency cone

```text
ParisiMin
   │
   └── full MIN existence
          │
ParisiQDeriv
   │
   └── ParisiMVariation          (new, §14.7 mass/split package)
          │
CoupledProp + CoupledLambdaZero + CoupledDeriv + CoupledSecondDeriv
          │
          └── ParisiMainEstimate (new, 14.8–14.10)

FiniteGibbs/Gaussian concentration + cascade recursion
          │
          └── ParisiConcentration (new, Prop 14.5.8)

ParisiMainEstimate + ParisiConcentration
          │
          └── ParisiLocalization (new, Prop 14.5.6)

ParisiLocalization + Guerra interpolation derivative
          │
          └── ParisiInterpolationLower (new, Thm 14.5.4 + endpoint helpers)

ParisiInterpolationLower + MIN
          │
          └── ParisiLowerBound (existing capstone)
                  │
                  ├── zero-field reduction (already present)
                  ├── convergence squeeze (already present)
                  └── liminf corollary (already present)
```

The exact new filenames are recommendations, but the dependency direction should remain acyclic.

---

## What should NOT be pulled into this dependency cone

Avoid making the Chapter 14 lower-bound proof depend on:

```text
Limit/AsymptoticGibbs
Limit/OverlapArray
Ghirlanda-Guerra limit theory
Panchenko ultrametricity
Aizenman-Sims-Starr
Dovbysh-Sudakov
```

Those are important elsewhere in the repository, but Talagrand's Chapter 14 proof is self-contained with the already existing cascade/coupling machinery.

---

## Talagrand-to-Lean status table

| Book statement | Existing Lean interface | Remaining work |
| --- | --- | --- |
| (14.83), (14.84), (14.89) | `randomFieldParisiX₀`, `randomFieldParisiFunctional`, `randomFieldParisiFunctional_eq_integral` | None: the outer site-law expectation is present. |
| Guerra bound (14.90) | `iidFieldMixedPSpinFreeEnergy_le_randomFieldParisiInf` | None under its explicit global differentiability hypotheses. |
| Definition 14.5.3, Lemma 14.5.5 | `exists_randomFieldParisiFunctional_lt_inf_add_of_talagrand`, `bddBelow_randomFieldParisiSet_of_talagrand`, `continuousOn_randomFieldParisiFunctional_overlapCube`, `exists_randomFieldParisiQMinimum_of_fixed_masses`, `randomFieldParisiFunctional_erase_adjacent_eq`, `exists_nearOptimal_randomFieldParisiQMinimizer` | Joint mass/overlap continuity on the closed mass domain, mass minimization, and equal-mass/endpoint-mass reduction. |
| Proposition 14.7.5, (14.222) | `randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin`, `iidExternalFieldParisiQ_strict_chain_and_eq_moment_of_isMin`, `exists_nearOptimal_randomFieldParisi_stationary` | Mass-coordinate variational consequences of full finite-dimensional minimality. |
| Proposition 14.6.3 | `coupled_bound_coupling_siteField`, `coupled_bound_coupling_zero_siteField`, `coupled_bound` | Integrable adapters for the shared i.i.d. site-field law and the particular MIN interpolation. |
| Coupled endpoint and lambda calculus | `CoupledLambdaZero`, `CoupledEndpoint`, `CoupledDeriv`, `pairSiteY₀_le_taylor` | Uniform strict improvement for Sections 14.8-14.10. |
| Theorem 14.5.7, (14.112) | Coupled bounds above | All seven main-estimate cases and a constant uniform in volume, interpolation time, and realizable constrained overlap. |
| Proposition 14.5.8 | Finite Gibbs concentration machinery outside Parisi | A constrained partition-ratio estimate with the required disorder law and integrability. |
| Proposition 14.5.6, (14.110), (14.111) | `gibbsPair`, `integral_gibbsPair_eq`, `integral_pairAvg` | Overlap localization from the main estimate and concentration, summed over the finite overlap range. |
| Theorem 14.5.4, (14.107) | `guerraBound`, `guerraBound_eq`, `integral_guerraBound`; `BranchLimit`, `LevelBoundLaw` | The derivative remainder, localization-based differential inequality, and convergence on each fixed interval below one. |
| (14.109), Theorem 14.5.2 | `eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy_of_nondegenerate` | Endpoint comparison and the limit of interpolation times approaching one, after Theorem 14.5.4. |
| Theorem 14.5.1, zero second moment | `externalFieldLaw_eq_dirac_zero_of_second_moment_eq_zero`, `abs_mixedPSpinFreeEnergy_sub_field_le`, `abs_parisiInf_sub_field_le` | None in the reduction itself; its nondegenerate lower-bound input remains incomplete. |

## Continuity and level reduction details

`ParisiParameterContinuity.lean` includes the plain Gaussian root expectation as an exponent-zero Cole-Hopf level. Changing all variances is bounded by a finite sum of one-level moduli, uniformly in both the spatial argument and the external field. Integrating this bound proves joint overlap continuity under finite first moment. It also proves continuity of the exponent at zero for a fixed linear-growth terminal function.

`ParisiLevelReduction.lean` deletes any zero-variance level and specializes this identity to consecutive equal overlaps while preserving the correction sum exactly. `ParisiCompactMin.lean` iterates this deletion until the overlap list is strict, with no increase in value or level count, then applies concrete q-stationarity and strict endpoint results. Joint continuity with changing terminal functions and mass lists remains necessary for minimization on the full closed mass domain.

---

## Architectural invariants to preserve

### Invariant 1 — field sharing

Two replicas in a quenched pair use the same realized external field. Never integrate each replica against an independent copy of μh.

### Invariant 2 — conditioning before concentration

Any Gaussian concentration argument in Proposition 14.5.8 should condition on the external field. This protects the finite-second-moment theorem from accidental sub-Gaussian/exponential-moment assumptions.

### Invariant 3 — strict MIN is semantic, not syntactic

Repeated masses/overlaps must be removed by a theorem proving the functional is unchanged, not simply by assuming strictness after compact minimization.

### Invariant 4 — constants must have the book's uniformity

The main/localization constants may depend on fixed data such as `ξ`, `μh`, `t₀`, `k,m,q`, but not on `N`, interpolation time within `[0,t₀]`, or exact realizable overlap `u`.

### Invariant 5 — lower bound before convergence

Do not prove convergence first and derive the lower bound from it. The existing architecture intentionally makes the eventual lower inequality primitive, then gets convergence by squeezing with Guerra's upper bound.

### Invariant 6 — final default build must cover the capstone

When completed, add `ParisiLowerBound` to the umbrella import so CI protects it.

---

## Practical “where to edit” summary

### First edits

`ParisiMin.lean`:

```text
closed domain
joint continuity
compact minimizer
redundant-level deletion
full MIN theorem
```

### Second edits/new file

`ParisiMVariation.lean` (recommended):

```text
split insertion
Φ / U / f
mass derivative identities
f bounds
q₁ lower bound
14.283
```

### Third edits/new file

`ParisiMainEstimate.lean`:

```text
seven coupled-copy cases
uniform K
14.112
```

### Fourth edits/new file

`ParisiConcentration.lean`:

```text
J/V/B recursion comparison
Gaussian Lipschitz/concentration
14.114
```

### Fifth edits/new file

`ParisiLocalization.lean`:

```text
sum exact overlap atoms
14.110-14.111
```

### Sixth edits/new file

`ParisiInterpolationLower.lean`:

```text
derivative remainder
Gronwall/differential inequality
14.107
14.109 endpoint helper
```

### Final edit

`ParisiLowerBound.lean`:

```text
assemble nondegenerate theorem
leave existing zero-field / convergence / liminf structure intact
```

Then update docs and `SpinGlass.lean`.

---

## Final architecture after completion

The intended final state is:

```text
finite-volume Gaussian/cascade machinery
          ↓
Guerra upper bound                  coupled-copy bound
          ↓                               ↓
Parisi infimum                      MIN + variational calculus
          │                               ↓
          │                         main estimate
          │                               ↓
          │                         concentration
          │                               ↓
          │                         localization
          │                               ↓
          │                         interpolation lower comparison
          │                               ↓
          └──────────────────────→ ParisiLowerBound
                                          ↓
                                    convergence theorem
```

This leaves the Chapter 15 structural theory independent and makes the Parisi formula available as a completed Chapter 14 theorem in the repository's existing random-field generality.
