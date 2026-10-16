# Lower-bound architecture

## Evidence and scope

The lower bound is complete as of 2026-10-13. All four original theorems
in `ParisiLowerBound.lean` compile with unchanged statements and assumptions.
The explicit combined capstone/main/interpolation build passed with 3794
jobs. All 61 public theorems in the seventeen completion owners and all four
capstone theorems have transitive axiom lists contained in `propext`,
`Classical.choice`, and `Quot.sound`. No proof holes remain under Parisi.

The exact finite interpolation identity now passes to the full cascade,
its Gaussian expectation, and its weight, field and time averages. The
remainder is identified with the physical constrained overlap/meeting
observable used by localization. Pressure averaging requires only a first
field moment. The original gap equals the remainder integral, including
both endpoints, and is nonnegative. A continuous integral majorant gives
Gronwall comparison without assuming differentiability of the gap or
continuity of the remainder. Curvature controls the final interpolation
interval. The uniform localization theorem selects MIN parameters and its
constant before the finite-volume accuracy; the bounded-field lower bound
then transfers through the existing field-truncation theorem.

The first structural refinement passed the complete repository and capstone
build with 3860 jobs, covering all then-current 308 Parisi modules. The audit of
all 2,874 public source declarations reports only standard Lean foundations.
Existing public statements and assumptions are unchanged. The later analytic
filename and topic refinement is recorded separately in
[the plan](EDITING_PLAN.md#analytic-topic-refinement); source and import checks
passed. Its complete repository, analytic library and capstone build passed on
2026-10-14 with 3863 jobs, covering all 311 current Parisi modules. The foundation
audit of all 2,874 public declarations, including the four capstone theorems,
also passed: 2,859 use only standard Lean foundations, fifteen use no axioms,
and there were no audit errors. All 215 analytic declaration names, namespaces,
normalized signatures and complete proof or definition bodies are preserved.

Exact completion owners and commands are recorded in
[the plan](EDITING_PLAN.md#next-task) and [INDEX.md](../INDEX.md).

## Consolidation contract

The validation records above establish compilation and foundations for their
recorded source states. They do not establish that every definition is canonical
or every source-attributed statement has optimal hypotheses and conclusions.
Apply the [milestone review](../AGENTS.md#milestone-review-before-a-pr) to future
changes; the [backlog](EDITING_PLAN.md#consolidation-backlog) names concrete targets.

Prefer one recursion valid on the closed mass domain, with a proved bridge to
the positive-mass cascade representation; one law-indexed functional, with
constant fields obtained by Dirac specialization; and derivatives of those
objects with proved response formulas. Signed conditional-square observables
should use the existing real integral API with their prefix/suffix meaning
explicit. These are consolidation targets, not claims that the current owners
already implement that organization.

Place general results in the existing Common/Mathlib layer when appropriate,
without dependencies back into Parisi. Preserve all four capstone contracts
while migrating internal APIs and their consumers. Historical requirements to
keep every analytic declaration body unchanged applied to the recorded file
reorganization; they do not prevent justified deduplication now.

The [2026-10-16 shared API refinement](EDITING_PLAN.md#shared-api-refinement)
places layer and tilt translations in Common Gaussian ColeHopf, and iterate
translation and concatenation in Common CascadeColeHopf, all in
`ProbabilityTheory`. QVariation consumes these owners without local copies.
The general within-domain measurable derivative theorem also supplies its
full-domain specialization. No dependency from Common back into Parisi was added.

## Historical validation ledger

The earlier milestone records below describe their then-current state.
References here to open stages or the former proof hole are superseded
by the completion evidence above and the current layer table below.

Proof checks: 2026-10-11, with Lean 4.34.0-rc2. The closed-competitor, actual root
and nonroot inner-mass U/f bridges, uniform propagated mass Taylor remainders,
square-root MIN estimates and variance-calculus leaves compile. The sharp spatial
invariant, uniform third derivatives, uniform first-overlap separation, bounded
U moments, second-moment variance control, cubic variance remainders and actual
endpoint curvature identities also compile. Axiom audits
of 213 public theorems in thirteen earlier owners and all 56 public theorems in
the five spatial/moment/endpoint owners, and all 24 public theorems in the three
new heat/dissipation/variance-Taylor owners contain only Lean's standard foundations.
The capstone audit still contains
`sorryAx`; full lower-bound completion is not certified. Exact commands and
remaining tasks are in [the plan](EDITING_PLAN.md#next-task).
Checks on 2026-10-12 additionally compile the profile modulus, uniform small
quadratic overlap remainder, root/nonroot curvature tolerance and actual
second-moment curvature tolerance. The outer-mass Taylor estimate includes the
terminal old mass one. These proofs preserve the profile and field contracts;
they do not assert a uniform third-profile-derivative bound or sixth-root rate.
The axiom audit of all 24 public theorems in the profile-remainder,
overlap-curvature and quantitative-mass owners reports only the three standard
foundations above; the separate capstone audit still reports `sorryAx`.
The outer-mass continuation also compiles its lower-mass endpoint comparison,
square-root mass derivative estimate, matched-layer complement identity,
actual left-split U/f bridge, variance/overlap calculus and convexity. The
mirror bound is $f_{\mathrm{left}}\le4\sqrt{M\varepsilon}$ with M depending only
on ξ, including the terminal matching mass one and k=0. The initial outer
moment is now identified with the old q-moment, yielding the admissible
U'(0)=q_L and f'(q_L)=0. The nonterminal right endpoint follows from original
mass-coordinate stationarity. Initial second moments transfer from the old
root/nonroot response, including the terminal index; their uniform curvature
tolerance transfers as well. Outer moments in [0,1], second-moment variance
Lipschitz coefficient 146, cubic U/f remainders and the actual mirror endpoint
second derivative compile. The mirror profile-coordinate remainder and
uniform critical response separation also compile. For each fixed $0\le t_0<1$,
the tolerance and overlap radius are selected before all MIN parameters and
times. Root/nonroot gaps are at least $(1-t_0)(q-u)/4$ near q; outer gaps are
at most $-(1-t_0)(u-q)/4$, including the terminal index. CoupledFieldTaylor
averages the coupling Taylor bound and proves the explicit gain with the
actual cascade zero-coupling expectation. CoupledResponseMoment now identifies
it with the actual squared suffix gradient, the unsplit outer initial moment,
and the matched split moments under independent field/root averages.
CoupledResponseGain identifies both time-dependent nonroot coupling slopes,
erases their matching split at zero coupling, and proves uniform near-overlap
one-site gains $(1-t_0)^2(u-q)^2/32$, including terminal outer mass one.
The concrete profile-dependent covariance witnesses and exact correction
now compile in CoupledParisiSplitVariance and CoupledParisiCorrection.
CoupledParisiComparison proves the finite-volume split comparison.
CoupledFieldPressure proves a coordinate field bound and finite-first-moment
integrability; CoupledRandomFieldComparison averages the i.i.d. quenched field
and proves its nearby split-pressure penalty.
CoupledAuxiliaryTransport proves the physical Gaussian projection law;
CoupledCascadeDeletion and CoupledCanonicalAuxiliary recover the original
masses, time-scaled variances and replica prefixes by deleting the zero mark.
CoupledTerminalNormalization integrates the last mass-one mark exactly,
and CoupledOriginalPressure identifies the original k-level pressure and
interpolation bracket. CoupledMainNear proves its nearby quadratic penalty
$(1-t_0)^2(u-q)^2/32$, with tolerance/radius preceding MIN parameters,
volume and time, and terminal outer coverage.
CoupledRootMassLimit and CoupledRootGain identify the actual positive root
insertion's value, slope and gain, and prove its zero-mass limits under the
preserved field law. CoupledRootVariance supplies the initial nonnegative
covariance witnesses, exact correction and deterministic auxiliary deletion.
CoupledRootComparison proves the finite-volume and i.i.d. field comparisons;
CoupledMainRoot takes the actual mass limit and proves the nearby root penalty.
CoupledRootNonnegative extends it to the whole nonnegative initial interval,
with pressure coefficient 1/8. CoupledIndependentPair provides the conditional
two-field recursion and its zero-mass gradient-product limit.
CoupledGaussianCorrelation proves the covariance comparison, including
one-sided endpoint calculus and the probability field average.
CoupledGaussianPairLaw identifies the concrete common/antisymmetric laws.
CoupledRootSignedResponse identifies the zero-overlap baseline and proves
uniform canonical signed response separation. CoupledSignedRootSite and
CoupledSignedRootLaw connect it to the actual independent-level recursion and
normalized signed-root law. CoupledRootSignedGain proves its concrete value,
slope, mass limit and Taylor gain, and CoupledRootSignedTransport identifies
the raw one-site comparison. CoupledRootSignedVariance supplies the signed
covariance, negative tangents and exact correction; CoupledRootSignedComparison
proves the finite-volume and i.i.d. field bounds. CoupledMainRootSigned completes
the whole initial interval, including negative overlaps, with coefficient 1/8.
The far nonroot inner case now compiles in CoupledMainInnerUniform. Its free
physical mass list admits a two-sided neighborhood of the matching mass,
without requiring a monotone scalar split list. Actual auxiliary deletion,
terminal normalization, finite-volume comparison, i.i.d. field averaging and
mass differentiation give the concrete derivative in (14.335). Strict profile
convexity and compactness give a tangent gap even when zero is an endpoint.
The uniform mass error selects the tolerance before every MIN, and a compact
cover of continuous scalar witnesses gives one positive pressure gap across
all nonroot inner levels, times, separated overlaps and volumes for each MIN.
The mirror far case now compiles in CoupledMainOuterUniform. Its scalar outer
mass is halved at the physical shared level, permitting variation above the
terminal scalar mass one. The concrete pressure, derivative, convexity
alternative, uniform tolerance and compact scalar cover are proved, including
k=0 and a collapsed terminal overlap interval. CoupledZeroTimeComparison
uses vanishing driven covariance to extend the comparison to all realizable
overlaps. CoupledMainZeroTime identifies the concrete stationary moment and
proves the zero-time quadratic penalty with coefficient 1/2 at every level.
The adjacent rearrangement and strict equality case now compile in
ParisiColeHopfSwap, including genuine mass zero and the actual strictly convex
recursive suffix with unordered masses in [0,1]. ParisiColeHopfRearrangement
extends this to finite sorting, active inversion strictness and field-averaged
scalar order rigidity, and identifies the original full-list comparator.
The paired Gaussian owners prove common/antisymmetric field rigidity, the
independent factorization, exact exponential and mass-zero integrals, unit
Lipschitz propagation, finite paired comparison and field average. A positive
correlated mark after an earlier independent nonzero mark gives a strict gap
at every field; arbitrary intervening layers are allowed. Two opposite
nonzero root directions also give a strict gap before any later positive
correlated mark, even when both root masses are zero. These are general finite
list results. The actual canonical labelled lists are now constructed,
including root and terminal splits, with a third root expectation when the
root interval is split. Physical sorting preserves both source lists and
the merged length is 2k+5. Actual interval variance sums and tied-mass Gaussian
regrouping recover the original full scalar recursion. The canonical one-site
field average is therefore at most twice the old closed Parisi value under a
finite first field moment. The actual labelled correction sum also equals
the old correction. Concrete mixed-mass witnesses give the magnitude gap,
and the proved actual common/signed root prefix gives the negative gap.
The combined one-site outside-neighbor comparison retains the initial
exception of Proposition 14.8.3. The merged scalar path is monotone in [0,1];
its signed matrix path stays in [-1,1], leaves auxiliary coordinates unchanged
and has zero terminal diagonal defect. Actual driven endpoints and clamped
profile increments now identify the signed Gaussian covariance columns.
The full matrix correction and raw coupled level sum equal t times the old
correction. The full zero-mass prefix is extracted, including the independent
split-root expectation; the actual positive suffix masses meet the cascade
admissibility API and retain the old correction. The compressed matrix,
concrete aggregate root columns, exact Gaussian root/positive laws and
canonical finite-volume comparison now compile. The actual positive site
cascade is identified with its full paired positive list. The complete root
expectation and site identity now compile in CoupledCanonicalRootRecursion.
The exact surviving auxiliary source and Gaussian maps, deletion of every
zero-contribution driven layer and original pressure normalization compile
in CoupledCanonicalAuxiliaryProjection, CoupledCascadeListDeletion,
CoupledCanonicalAuxiliaryTransport and CoupledCanonicalPressure.
CoupledCanonicalFieldComparison averages the actual physical pressure under
the finite-first-moment i.i.d. field law. CoupledMainOutside proves a positive
outside-neighbor physical gap at each fixed interior time and overlap, before
all volumes and Gaussian realizations. CoupledPairVarianceContinuity supplies
the actual paired modulus through the full list and field average;
CoupledCanonicalContinuity specializes it to joint time/magnitude continuity.
The actual arbitrary-coupling terminal, complete site identity and continuity
now compile in CoupledPairTerminal and CoupledCanonicalCoupling. Closed split
strictness compiles in CoupledCanonicalClosedGap. CoupledCanonicalZeroTime
identifies the actual auxiliary law, stationary q-moment and quadratic
coupling witness at time zero. CoupledCanonicalTrialComparison gives the
exact tangent-defect comparison when the trial and realized overlaps differ,
with a continuous scalar bound on the original physical pressure.
CoupledMainOutsideCompact and CoupledMainOutsideUniform prove one physical
gap on compact separated outside regions before all original levels, times,
overlaps, volumes and Gaussian laws, including time zero. The neighboring
boundaries and initial root strip remain separate main-estimate cases.
CoupledGaussianSiteContinuity supplies the actual arbitrary-coupling
root/positive-variance continuity needed for free-mass fixed trials.
The latest explicit leaf/consumer build passed on 2026-10-13 with 3703 jobs.
The expanded audit of 532 supporting declarations in 68 coupled owners and
ten variational owners, including the public zero-coupling measurability
declaration, reports only standard Lean foundations. A further audit of
41 canonical witness, strictness and path theorems also reports only
standard Lean foundations. An additional audit of all 38 endpoint, covariance,
matrix correction and root-extraction theorems also uses only those foundations.
An additional audit of all 42 compressed comparison and Gaussian recursion
theorems reports the same foundations.
All 54 further root, physical-pressure, field-comparison and continuity
theorems also use only those foundations.
All 45 arbitrary-coupling, zero-time, fixed-trial and compact outside
theorems use only those foundations as well.
The unchanged nondegenerate capstone still reports `sorryAx`. Exact commands
are recorded in the plan. Fixed-trial free-mass and signed-root witnesses
must cover the remaining boundary strips before full main-estimate assembly.
[INDEX.md](../INDEX.md) owns the declaration-to-file map; [the plan](EDITING_PLAN.md)
owns pending tasks and source pages.

## Current layer status

The completion scan finds no proof holes under SpinGlass/Parisi. The
capstone's complete dependency cone uses only standard Lean foundations.
The layer table combines the earlier checked interfaces with the completed
interpolation and lower-bound assembly.

| Layer | Source state | Consumer |
| --- | --- | --- |
| Random-field functional and optimized Guerra upper bound | Implemented | MIN selection and eventual squeeze |
| Concrete q-derivative and law-level stationarity | Implemented | Strict endpoints and mass calculus |
| Full fixed-level MIN existence | Implemented | Mass variations and main estimate |
| Left/right split constructors and functional identities | Implemented | Inserted-mass derivatives |
| Both splits' closed-domain membership | Compiled | Split competitor bound |
| Generic analytic tools | 215 unchanged declarations in mathematical topic owners, imported by Analytic.lean | Mass, variance, concentration and interpolation bridges |
| Closed-competitor global lower bound and quantitative split comparison | Compiled | Mass derivative estimates |
| Concrete mass derivative and field/root averaging | Compiled, including zero mass and one-sided mass endpoints | U/f calculus |
| Initial root split, its closed-domain identities and mass derivative | Compiled | Initial-interval U/f calculus |
| Actual suffix C4 regularity, local variance response and moments | Compiled, including zero masses and variances | Fixed-prefix calculus |
| Fixed-prefix variance derivatives, probability-law averaging, concavity | Compiled; positive matching mass for spatial measurability after the prefix | U/f identification |
| Root and nonroot inner-mass U/f identification, q-stationarity, f endpoints | Compiled; nonroot left endpoint uses fixed-level mass minimality | Quantitative mass variation |
| Ordered-prefix mass Taylor remainder, actual functional specialization, root/nonroot inner-mass (14.264) | Compiled; constants depend only on the total ξ variance ceiling, including field averaging and closed endpoints | Overlap curvature |
| Sharp spatial invariant, value increments and lower curvature | Compiled, including zero mass and variance | Uniform first overlap and spatial moments |
| Uniform third spatial derivatives through ordered log-cosh recursion | Compiled with sufficient coefficient twelve; book coefficient four is not asserted | Cubic overlap remainder |
| Uniform first-overlap separation under nondegenerate probability field law | Compiled, coefficient chosen before MIN parameters | Initial overlap cases |
| Concrete U moments and response derivative bounds | Compiled; moments in [0,1], U' in [0,1], U'' in [-1,0], first moment uniformly Lipschitz | Uniform variance curvature control |
| Actual root/nonroot endpoint second derivatives | Compiled from q-stationarity and the second spatial moment | Quantitative curvature |
| Two-derivative heat calculus and actual squared-curvature dissipation | Compiled with C4 terminal regularity, including zero mass and both variance endpoints | Second-moment variance control |
| Uniform second-moment variance control | Compiled with coefficient 146 for both mass orientations after fixed-prefix and probability-law averages | Cubic response remainder |
| Actual root/nonroot and outer U and stationary f cubic variance remainders | Compiled with exact profile corrections | Overlap-coordinate conversion |
| Profile-coordinate remainder and uniform quantitative curvature | Compiled using the compact ξ'' modulus and first-overlap separation; for every κ>0, select MIN tolerance before its parameters; sixth-root rate is not asserted | Near-overlap main-estimate cases |
| Outer-mass Taylor estimate | Compiled uniformly, including terminal old mass one and k=0 | Mirror slope estimate |
| Outer-mass lower endpoint comparison, concrete mirror U/f bridge and square-root estimate | Compiled, including terminal matching mass one and k=0; full prefix/field variance calculus and convexity | Mirror endpoint and main-estimate cases |
| Mirror initial moments, q-stationarity, nonterminal f right endpoint and endpoint curvature | Compiled; actual cascade transport, initial second moments and uniform curvature tolerance include the terminal index and k=0 | Mirror profile conversion and main-estimate cases |
| Mirror profile-coordinate remainder | Compiled with a left-endpoint compact ξ'' modulus and actual stationary f; terminal interval included | Mirror main-estimate cases |
| Uniform critical response gap | Compiled for root, nonroot and outer moments; tolerance/radius precede all parameters and times; terminal outer included | Critical coupled cases |
| Common-field coupling Taylor and explicit gain | Compiled under zero-coupling integrability; concrete cascade specialization needs only finite first field moment | Coupled-to-response identification |
| Coupled signed conditional square and actual matched split moments | Compiled; unsplit initial outer moment, closed split endpoints, field/root Fubini and terminal mass one included | Time-dependent coupling |
| Concrete inner/outer time-dependent one-site coupling gain | Compiled; actual slopes and zero value, uniform tolerance/radius and quadratic coefficient 1/32 | Finite-volume coupled comparison |
| Separate driven/auxiliary Gaussian witnesses and law transport | Compiled general finite-volume bound, total-variance Gaussian law and full one-site recursion transport; zero driven/total variance included | Concrete profile/canonical-cascade specialization |
| Concrete finite-volume split comparison and i.i.d. field average | Compiled; actual variances/covariances, exact correction, coordinate field bound and first-moment integrability | Original physical pressure |
| Original auxiliary law, zero insertion deletion and terminal normalization | Compiled; original k-level pressure and interpolation bracket identified | Main-estimate cases |
| Nearby nonroot and outer main-estimate cases | Compiled with quadratic coefficient 1/32, uniform tolerance/radius and terminal outer coverage | Full main estimate |
| Positive root insertion and its zero-mass pressure limit | Compiled; actual one-site value/slope, covariance and correction witnesses, auxiliary deletion and i.i.d. field average | Root pressure gain |
| Nearby root main-estimate case | Compiled with coefficient 1/32 and tolerance/radius preceding parameters, volume and time; negative root overlaps excluded | Full initial interval |
| Whole nonnegative initial interval | Compiled with pressure coefficient 1/8 and tolerance preceding parameters, volume and time | Full initial interval |
| Two-field recursion and signed covariance response | Compiled conditional and averaged value/slope/Taylor, actual mass limit, Gaussian laws and raw recursion identification | Signed finite-volume comparison |
| Whole initial overlap interval, including negative overlaps | Compiled with pressure coefficient 1/8, exact correction, terminal normalization and i.i.d. field average | Remaining main-estimate cases |
| Uniform far nonroot inner intervals, Proposition 14.8.2 | Compiled; actual free coupled mass, derivative, strict tangent gap and compact scalar cover; tolerance before all MINs | Full main estimate |
| Uniform far outer intervals, Proposition 14.8.5 | Compiled; scalar masses above one permitted by physical halving; terminal index, k=0 and collapsed terminal interval included | Full main estimate |
| Zero time at every realizable overlap, Proposition 14.8.7 | Compiled with quadratic coefficient 1/2 from actual stationary moment, including negative overlaps and every level | Full main estimate |
| Positive time outside neighboring intervals, Proposition 14.8.6 | Arbitrary-coupling site identity, every closed split, fixed-trial tangent-defect comparison and compact uniform physical gaps on separated outside regions compile; neighboring-boundary strips and initial root exception still require the other trial families | Full main estimate |
| Zero-time scalar witness for compactness | Actual canonical auxiliary law, stationary q-moment coupling slope and quadratic scalar gap compile at every split and sign | CoupledMainOutsideCompact |
| Uniform main estimate, Theorem 14.5.7 | Compiled in CoupledMainEstimate; all closed boundaries and both root signs, with tolerance before MIN and one constant before volume/time/level/overlap | Concentration and localization |
| Pressure-gap to small constrained mass, Proposition 14.5.8 | Bounded-field version compiled in ParisiBranchConcentration: actual canonical Gaussian/tree joint mass, exact physical pressure gap and uniform rate; arbitrary field laws use the separate lower-bound truncation reduction | Localization and identification with the Guerra interpolation |
| Uniform overlap localization and second moments | Compiled in Localization; exact physical meeting-mass normalization and accuracy quantifiers | Remainder control |
| Signed profile remainder and localized bound | Compiled in Interpolation/LocalizedRemainder; uniform curvature bound and positive pressure-gap estimate | Exact interpolation identity |
| Fixed-law pressure and initial/terminal endpoints | Compiled; actual recursion/tree expectation, first-moment integrability, affine bracket and quenched free-energy endpoint | Infinite-tree interpolation |
| Finite weighted and actual truncated-tree derivative | Compiled; exact closed-interval integral formula retains the profile remainder | Infinite-cascade limit and physical remainder identification |
| Infinite-tree identity and interpolation lower comparison | Compiled in IntegralIdentity, GapBounds, IntegralGronwall and LowerComparison; first-moment pressure averaging and actual remainder laws | BoundedLowerBound |
| Bounded nondegenerate lower bound and field truncation | Compiled in BoundedLowerBound and the original capstone | General lower bound |
| General lower bound, convergence, liminf | All four capstone theorems compiled and audited under preserved assumptions | Final result |

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

Arrows below describe the completed mathematical dependencies. Exact import
dependencies are in the code.

```text
Field + recursion + Guerra upper bound -> ParisiInf
ParisiInf + continuity + level reduction -> compact MIN -> strict full MIN
Concrete QVariation -------------------------------> stationarity
Full MIN + stationarity + split identities -> mass/variance calculus [compiled]
Coupled core + response gap + actual Gaussian moment bridge -> main estimate [compiled]
Finite Gibbs + cascade + bounded-field fluctuations -> pair-mass concentration [compiled]
Pair-mass concentration + original branch/pressure identification -> bounded-field Proposition 14.5.8 [compiled]
Main estimate + concentration -> localization and physical remainder bounds [compiled]
Weighted Gaussian derivative + actual tree covariance -> exact truncated-tree remainder [compiled]
Truncated-tree limit + joint-law identification -> exact infinite-tree remainder [compiled]
Localization + exact infinite-tree remainder -> interpolation lower comparison [compiled]
Interpolation + endpoint bound -> bounded nondegenerate lower bound [compiled]
Bounded lower bound + field truncation -> nondegenerate lower bound [compiled]
Nondegenerate bound + field continuity -> general eventual lower bound
General bound + existing upper bound -> convergence -> liminf
```

Concentration consumes a pressure-gap hypothesis; it need not import the main
estimate. Localization joins those two branches. Keep the lower-bound capstone
an assembly layer. New file names in the plan are proposals, not existing APIs.

### Standalone analytic inputs

The 27 modules under [Analytic](../Analytic/) depend only on Mathlib and other
analytic owners. They retain all 215 original public declarations in the
`SpinGlass.Aristotle` namespaces. [Analytic.lean](../Analytic.lean) imports the
topic owners and preserves the original Mathlib availability. Replace the
historical `SpinGlass.Parisi.ARISTOTLE` import with `SpinGlass.Parisi.Analytic`.
The [topic guide](ANALYTIC.md#topic-owners) identifies each owner and dependency.

Mass/Basic owns the transform and tilted moments; Mass/Derivatives establishes
mass calculus, and Mass/Bounds collects estimates. This branch is independent
of heat calculus. The Heat sequence runs through Basic, Taylor, Backward, Jet
and Split. Gaussian/Split combines those identities with mass bounds, while
Gaussian/Integrability, Gaussian/Differentiation and Gaussian/Curvature own the
other Gaussian tools. Generic weighted integral concavity and derivative-to-
Lipschitz estimates belong to Convexity and Lipschitz, before their Gaussian
specializations. Profile, field truncation, bounded differences,
concentration, compactness, localization and interpolation form separate branches.
Concrete consumers import only the analytic topics they use.

The project bridges identify these generic quantities with the actual recursion,
discharge regularity and domination, propagate derivatives through baseline
weights and field averaging, and establish the physical pressure identities.
The lower-bound chain is complete. Generic lemmas retain their explicit analytic
hypotheses for other applications.

Field/FieldMoments.lean owns the nondegenerate site law and finite-second-moment
consequences independently of overlap calculus. Parameters owns the elementary
theta derivative. Compact minimization imports parameters and recursion directly;
strict mass extraction imports random-field stationarity explicitly. Coupled
compactness and main-estimate proofs share one finite positive-bound helper and
one positive/signed root-trial bridge.

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

Variational/ParisiMVariation.lean contains both split orientations, endpoint/
matching-mass identities, domain membership, global-infimum bounds, and
quantitative near-minimality inequalities. It now consumes the concrete
mass-coordinate derivative from ParisiMassRecursion.lean. The right constructor
addresses nonterminal intervals. ParisiRootMVariation.lean covers the initial
interval $[0,q_1]$, with mass and overlap cons constructors, domain membership,
zero-mass and empty-interval functional identities, and the root mass derivative.

The first mass derivative uses the actual suffix and preceding cascade tilt,
then the independent root Gaussian and site-law integral. A finite first field
moment suffices. Empty inserted intervals have zero mass derivative in either
orientation. Uniform first-derivative bounds survive cascade transport. The
uniform mass Taylor bound is propagated through the entire ordered prefix in
ParisiMassPropagation.lean and specialized to both split orientations in
ParisiQuantitativeMass.lean.

### Variance response

ParisiSpatialRegularity.lean proves C4 regularity and bounded spatial derivatives
for the actual log-cosh terminal and every finite suffix, including zero masses
and variances. Its one-layer first/second spatial bounds are uniform in variance.
The suffix bound used here may depend on its fixed parameters; it is not the
book's global MIN Taylor constant.

ParisiVarianceResponse.lean defines the actual local inserted-mass response and
squared spatial moments under `coleHopfQ`. Matching masses erase the split on
the admissible closed variance interval. The preceding cascade law is therefore
fixed in variance. ParisiVariancePropagation.lean differentiates its response
and first moment, then averages those identities over an arbitrary fixed
probability law of a measurable evaluation point. Both variance endpoints are
treated within the interval. The local zero-mass branch is covered separately
by ParisiVarianceAveraging.lean; prefix spatial measurability currently uses a
positive matching mass, as appropriate for nonroot strict MIN intervals.

The full response has a variance-ceiling bound independent of the preceding
level count and parameters. ParisiSplitResponse.lean identifies them with
`splitParisiRightMassDeriv` and `splitParisiRootMassDeriv`, including the
field/root nesting and q-stationary moment at zero variance. The outer-mass
orientation is now identified in ParisiOuterSplitResponse.lean, after the
matched-layer semigroup complement proved in ParisiOuterMassResponse.lean.
Its variance derivatives have positive curvature, and its overlap derivative
is $\xi''(u)(M_1(w)-u)$ with $w=\xi'(u)-\xi'(q_L)$. Both variance endpoints
are admissible. ParisiCascadeTransport.lean integrates the last Gaussian mark
through its actual cascade density. ParisiOuterEndpoints.lean identifies the
initial outer moment with the old q-moment and the initial second moment with
the preceding root/nonroot one. Thus U'(0)=q_L, f'(q_L)=0, and the curvature
formula $f''(q_L)=\xi''(q_L)(\xi''(q_L)M_2(0)-1)$ follow from actual
law-level stationarity, within the admissible interval. Nonterminal f(q_R)=0
follows from fixed-level mass stationarity. The terminal old mass one is included
in the response, functional identity, lower-mass comparison and uniform
square-root estimate; it is not a free interior mass coordinate of the old
functional. Both orientations have bounded first/second moments, second-moment
variance Lipschitz coefficient 146, and cubic variance U/f remainders. The
uniform second-moment curvature tolerance is also transferred to every outer
overlap. The mirror overlap-coordinate remainder now follows from the compact
profile modulus and the actual variance remainder. The global mass Taylor
remainder is compiled.

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

CoupledFieldTaylor.lean propagates field integrability from zero coupling,
averages `pairSiteY₀_le_taylor`, and proves the explicit λ=−β gain β²/2.
Its concrete specialization identifies the zero value and slope with the
actual log-cosh recursion and cascade tilted square, using only a finite
first field moment. ParisiCriticalResponse.lean gives the needed scalar
linear gap, with tolerance and radius uniform in the MIN parameters.
CoupledResponseMoment proves the signed conditional-square identity from the
Cole-Hopf derivative and normalized cascade weights, with all zero Gaussian
variances included. Its matched split arrays have positive monotone masses
bounded by one. The actual initial outer moment, complementary inner/outer
moments, independent field/root averages and law-level slopes are identified.
CoupledResponseGain proves the time-dependent inner/outer coupling derivative,
the original zero value and the uniform quadratic one-site gain. The selected
tolerance/radius precede all MIN parameters and times; terminal outer mass one
is included. CoupledVarianceWitness supplies normalized independent factors
with freely chosen total mark variance, avoiding a positive driven-variance
requirement. CoupledGaussianMix proves their exact two-column Gaussian law
and transports the full one-site recursion, then applies this transport to
the general finite-volume coupled bound. The concrete variance/covariance
instantiation, field-law pressure comparison, physical Gaussian projection,
zero-mark deletion and terminal normalization now compile. CoupledMainNear
proves the nearby original-pressure penalty with coefficient 1/32.
CoupledRootMassLimit through CoupledMainRoot now supply the positive
inserted-root value/slope limits and actual finite-volume pressure limit for
nonnegative initial overlaps. CoupledRootNonnegative extends the pressure
penalty to the whole interval with coefficient 1/8. The canonical signed
response and Gaussian-law estimate now compile in CoupledRootSignedResponse
and its dependencies. CoupledMainRootSigned applies the actual signed mass
limit and completes the whole initial-interval physical-pressure estimate.
The cascade API still must not be used directly at mass zero. The far inner,
far outer and zero-time cases are complete. Canonical positive-time
outside-neighbor comparison and full uniform assembly are still needed.

### Random-field concentration and the bounded-law reduction

On printed page 381, following (14.123), Talagrand finishes the displayed
concentration proof for deterministic site fields and points to additional
martingale-difference work for random non-Gaussian fields.

Conditioning on the site vector allows Gaussian concentration around a
conditional mean. The main estimate supplies a law-averaged pressure gap.
One cannot replace that conditional mean by its law average without another
argument. A Lipschitz bound uniform in the field realization does not close this
gap by itself.

ProductSubGaussian and PairTiltCombinedConcentration now prove this additional
field-fluctuation control for bounded site laws. ParisiBranchConcentration
specializes it to the original physical parameters and proves uniform
exponential decay from the normalized pressure gap, including the exact
tree-meeting identity. A finite second moment alone is not a generic
exponential-concentration hypothesis. FieldTruncation supplies a uniform
approximation of the lower-bound target; it can be applied after the
bounded-law localization, interpolation and endpoint arguments are complete.

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

SpinGlass.lean imports SpinGlass/Parisi.lean. The convenience module now reaches
every Lean module under Parisi, including ParisiLowerBound.lean, the compatibility
analytic umbrella and independent auxiliary leaves. Its import graph has no
cycles. Use the convenience module for client code and complete build coverage;
proof leaves import their declaration owners directly.

The structural refinement preserves all 2,848 existing public source-header
groups, including declarations moved to new owners. The current validation record
and exact commands are in [the plan](EDITING_PLAN.md#historical-structure-and-proof-refinement).

The toolchain is specified in lean-toolchain. lakefile.toml places packages and
build output under the parent workspace's .lake/spinglass directory and disables
automatic implicit binders. Do not reconfigure these paths for an isolated task.

When a stage changes, update its row here and the next task in the plan. Record
actual build evidence with the checked files/revision; do not carry forward
historical claims that a renamed module builds.
