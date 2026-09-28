# Lower-bound architecture

## Evidence and scope

Source inventory: 2026-09-27, after the directory reorganization. This inventory
comes from reading current declarations, imports, and proof-hole searches; it
does not certify a fresh Lean build. Validation commands are in [AGENTS.md](../AGENTS.md).
[INDEX.md](../INDEX.md) owns the declaration-to-file map; [the plan](EDITING_PLAN.md)
owns pending tasks and source pages.

A scan of Lean files under SpinGlass/Parisi finds one `sorry`, in the nondegenerate
theorem of [ParisiLowerBound.lean](../ParisiLowerBound.lean). Other missing stages
have no declarations yet, so counting holes understates the remaining work.
Implemented below means a proof body is present, not an independent mathematical
audit or a recorded successful build.

| Layer | Source state | Consumer |
| --- | --- | --- |
| Random-field functional and optimized Guerra upper bound | Implemented | MIN selection and eventual squeeze |
| Concrete q-derivative and law-level stationarity | Implemented | Strict endpoints and mass calculus |
| Full fixed-level MIN existence | Implemented | Mass variations and main estimate |
| Left/right split constructors and functional identities | Implemented | Inserted-mass derivatives |
| Left split's closed-domain membership | Implemented | Split competitor bound |
| Standalone analytic tools in ARISTOTLE | Leaf build and all 199 theorem axiom audits passed on 2026-09-28; see [application map](ARISTOTLE.md) | Generic inputs to the open layers below; concrete bridges pending |
| Closed-competitor global lower bound and quantitative split comparison | Next task | Mass derivative estimates |
| Mass derivative, U/f calculus, quantitative curvature | Open | Main-estimate cases |
| Coupled bound, zero coupling, first derivative, Taylor control | Implemented core; final adapters pending | Main estimate |
| Uniform main estimate, Theorem 14.5.7 | Open | Localization |
| Pressure-gap to small constrained mass, Proposition 14.5.8 | Open; random-field transfer needs proof | Localization |
| Localization and interpolation lower comparison | Open | Nondegenerate capstone |
| General lower bound, convergence, liminf | Implemented reductions depending on the capstone hole | Final result |

## Formal target

The nondegenerate theorem has exactly this contract:

```lean
theorem eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy_of_nondegenerate
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : NondegenerateExternalFieldLaw μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hPSD : ∀ N : ℕ, (overlapCovMatrix N ξ).PosSemidef) :
    ∀ ε > 0, ∀ᶠ N in atTop,
      randomFieldParisiInf μh ξ - ε ≤ iidFieldMixedPSpinFreeEnergy N μh ξ
```

The general eventual theorem replaces nondegeneracy by integrability of the
squared field. Its zero-second-moment case uses identification with the Dirac
law at zero and continuity in a constant field. Both convergence and liminf
corollaries additionally assume `Differentiable` ℝ ξ and deriv ξ 0 = 0, as required
by the current Guerra API. Preserve those signatures; the lower-bound target
itself does not include these additional hypotheses.

For field assumptions, (14.65) on printed p. 363 specifies i.i.d. copies of a
random variable, and p. 373 identifies the nonzero-field branch with positive
second moment. The finite-second-moment integrability requirement is explicit
in the current Lean contract, not in the displayed definition (14.65). The book
explicitly discusses non-Gaussian random fields on p. 381; retain that scope.

`TalagrandXiCondition` lives in Minimizer/QVariation/Parameters.lean. It records
evenness, global convexity, continuity of the first derivative on [0,1], first
and second derivative existence there, positive second derivative away from
zero, and third derivative existence/nonnegativity on (0,1]. Required stronger
regularity must be proved from that interface. Covariance PSD remains separate.

## Dependency map

Solid arrows below describe the intended mathematical dependencies, including
stages that have not been implemented. Exact import dependencies are in the code.

```text
Field + recursion + Guerra upper bound -> ParisiInf
ParisiInf + continuity + level reduction -> compact MIN -> strict full MIN
Concrete QVariation -------------------------------> stationarity
Full MIN + stationarity + split identities -> mass calculus [open]
Coupled core + mass calculus -> uniform main estimate [open]
Finite Gibbs + cascade + field fluctuation control -> concentration [open]
Main estimate + concentration -> localization [open]
Localization + exact Guerra remainder -> interpolation lower comparison [open]
Interpolation + endpoint bound -> nondegenerate lower bound [hole]
Nondegenerate bound + field continuity -> general eventual lower bound
General bound + existing upper bound -> convergence -> liminf
```

Concentration consumes a pressure-gap hypothesis; it need not import the main
estimate. Localization joins those two branches. Keep the lower-bound capstone
an assembly layer. New file names in the plan are proposals, not existing APIs.

### Standalone analytic inputs

[ARISTOTLE.lean](../ARISTOTLE.lean) imports only Mathlib. Its local mass transform,
Gaussian split response, and spatial moments have explicit integral definitions.
The file includes zero-mass calculus, variance derivatives within closed
intervals, scalar variation estimates, curvature propagation, bounded-difference
exponential moments, truncation, and generic localization/endpoint assembly.
The [guide](ARISTOTLE.md) gives exact entry points and validation evidence.

No project module currently imports this file. To consume its results, prove
agreement with the project recursion and establish their smoothness, domination,
continuity, and uniformity hypotheses from the existing contracts. In particular,
single-layer split concavity still needs propagation through earlier layers;
bounded-field concentration still needs estimates for the actual cascade
logarithmic product and its conditional mean; truncation still needs uniform
law-level functional and free-energy continuity. The open-layer rows above
refer to these concrete obligations.

## Interfaces that matter

### MIN and closed-domain competitors

Minimizer/Compact.lean defines the mass/parameter domains and the closed
functional, including the zero-mass recursion. Minimizer/Full.lean returns
strict admissible lists, a value less than the global infimum plus the selected
tolerance, a q-minimizer, and full `IsMinOn` over the closed domain at that count.

The q-minimizer and the full minimum serve different roles. Use full minimality
for fixed-count mass variations. For an insertion, the count increases: combine
the global-infimum lower bound for that competitor with the original near-minimum.
Full MIN alone does not compare these two counts.

Variational/ParisiMVariation.lean contains both split orientations and endpoint/
matching-mass identities. The left split's mass, overlap, and pair membership
lemmas are present. The right constructor currently addresses nonterminal
intervals. Reuse the functional identities; isolate endpoint admissibility and
index conversion before the analysis.

### Concrete q-stationarity

The law-level result is
randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin. The companion
`iidExternalFieldParisiQ_strict_chain_and_eq_moment_of_isMin` explicitly identifies
the moment with a product-coordinate expectation. This layer provides endpoint
strictness and the moment identity for the actual recursion.

Maintain the root instructions' q-derivative audit conditions: actual recursion
moments, differentiation under the probability-law integral, admissible endpoint
variations, nondegeneracy-based first-moment positivity, strict final-moment
boundedness, and no assumed derivative identity in the book-level conclusion.

### Coupled and field interfaces

Conditional interpolation accepts a realized site field; law-level results
integrate against externalFieldVecLaw. Replicas share that realization through
sharedReplicaSiteField. Existing `randomField_coupling_rhs_zero_eq` and
`hasDerivAt_randomFieldPairSiteY₀_coupling_zero` already supply some averaged
adapters. Check their exact hypotheses before creating another one.

The first derivative, zero-coupling evaluation, and `pairSiteY₀_le_taylor` support
the main estimate. Remaining work includes parameter witnesses for each case,
integrable field averaging in the needed shape, and identification with the
mass-variation calculus. Generic coupled bounds do not yet prove the uniform
quadratic penalty.

### Random-field concentration is an explicit gap

On printed page 381, following (14.123), Talagrand finishes the displayed
concentration proof for deterministic site fields and points to additional
martingale-difference work for random non-Gaussian fields.

Conditioning on the site vector allows Gaussian concentration around a
conditional mean. The main estimate supplies a law-averaged pressure gap.
One cannot replace that conditional mean by its law average without another
argument. A Lipschitz bound uniform in the field realization does not close this
gap by itself.

The implementation must prove field-fluctuation control under the actual
moment assumptions, or prove an approximation/reduction that removes stronger
intermediate assumptions. A finite second moment alone is not a generic
exponential-concentration hypothesis. The plan records this obligation rather
than treating it as an available theorem.

## Quantifier contracts

| Result | Order of choices and uniformity |
| --- | --- |
| Theorem 14.5.7 | Fix profile, law, and time cutoff below 1; choose positive MIN tolerance; for each eligible MIN choose K; then quantify over volume, time, level, and overlap |
| Proposition 14.5.8 | Fix parameters and positive pressure gap; its constant may depend on that gap, but not volume/time/overlap |
| Proposition 14.5.6 | Choose localization K before the auxiliary tolerance; the volume threshold may depend on that tolerance; it must work uniformly over the time interval and finitely many levels |
| Theorem 14.5.4 | Fix cutoff and eligible MIN; take volume large for each requested interpolation accuracy |
| Endpoint passage | Choose cutoff close to 1, select eligible MIN, then choose volume large; do not choose MIN first and demand all later cutoffs |

Strict endpoint q-values do not supply the quantitative lower bound on the first
overlap needed in the critical cases. Likewise, pointwise strict improvement
does not supply a uniform quadratic penalty; use compactness with the required
continuity or upper semicontinuity.

## Build coverage and maintenance

SpinGlass.lean imports SpinGlass/Parisi.lean. That convenience module imports
MIN and the initial mass-variation file but omits ParisiLowerBound.lean.
It also omits ARISTOTLE.lean, whose explicit leaf validation is recorded in
[its guide](ARISTOTLE.md#validation).
Successful umbrella builds alone therefore do not certify the capstone. After
proof completion, include it in that import chain and run the explicit leaf and
full builds.

The toolchain is specified in lean-toolchain. lakefile.toml places packages and
build output under the parent workspace's .lake/spinglass directory and disables
automatic implicit binders. Do not reconfigure these paths for an isolated task.

When a stage changes, update its row here and the next task in the plan. Record
actual build evidence with the checked files/revision; do not carry forward
historical claims that a renamed module builds.
