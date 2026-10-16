# Lower-bound execution plan

## Goal and current frontier

Fill the existing nondegenerate eventual lower-bound theorem in
[ParisiLowerBound.lean](../ParisiLowerBound.lean), preserving every claim there.
Follow Talagrand, Vol. II, Sections 14.5-14.10. Source status is recorded in
[Architecture](ARCHITECTURE.md); declaration owners are in [INDEX.md](../INDEX.md).

Completed on 2026-10-13: all four capstone theorems compile with their
original statements and assumptions. The explicit combined build passed
with 3794 jobs. A transitive audit of the 61 new public theorems and four
capstone theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof holes under Parisi.

## Historical implementation overview

The following records describe the state at each earlier milestone. Their
references to open stages or the former capstone hole are historical;
the completion record and next-task section supersede them.

Verified on 2026-10-11 with Lean 4.34.0-rc2: the actual root and nonroot inner-mass
U/f bridges, mass stationarity, f endpoints, uniform propagated mass remainders,
root/nonroot inner-mass square-root estimates, and variance calculus compile.
Sharp spatial bounds, uniform third spatial derivatives, first-overlap
separation, bounded concrete U moments, second-moment variance control, cubic
variance remainders and endpoint curvature identities now also compile. Checks
on 2026-10-12 also compile the profile modulus, uniform small quadratic overlap
remainder, curvature tolerance and second-moment curvature tolerance, without
strengthening the profile contract. The outer-mass Taylor bound, lower-mass
endpoint comparison, mirror square-root bound and actual U/f bridge now also
compile, including the terminal old mass one and k=0. The complement identity
and full prefix/field variance calculus are proved in ParisiOuterMassResponse;
the actual left-split arrays and overlap calculus are in ParisiOuterSplitResponse.
ParisiCascadeTransport now integrates the actual final prefix weight, and
ParisiOuterEndpoints identifies initial outer first/second moments with the
preceding root/nonroot moments. U'(0)=q_L and f'(q_L)=0 hold at every outer
overlap; nonterminal f(q_R)=0 follows from original mass stationarity. The
outer moment bounds, coefficient 146 variance control, cubic U/f remainders,
endpoint second derivative and transferred uniform second-moment curvature
tolerance and mirror profile-coordinate remainder also compile. The capstone
still has its original `sorry`. ParisiCriticalResponse
proves uniform linear response separation for both orientations with tolerance
and radius selected before all parameters and times up to a fixed t₀<1.
CoupledFieldTaylor proves the common-field coupling Taylor bound and explicit
gain from the actual zero-coupling cascade expectation. CoupledResponseMoment
now identifies the signed conditional square with the actual prefix/suffix
gradient moment and the inner/outer matched split moments after field/root
averaging. CoupledResponseGain proves the actual time-dependent nonroot
coupling slopes, the original zero value and uniform quadratic one-site gains,
including the terminal outer interval. The concrete finite-volume comparison,
i.i.d. field average and original auxiliary cascade normalization now compile.
CoupledMainNear proves the nearby nonroot/outer pressure penalty. The actual
positive root insertion, its zero-mass limit and the nearby root pressure
penalty now compile in CoupledMainRoot and its dependencies.
CoupledRootNonnegative proves the whole nonnegative interval with coefficient
1/8. The conditional two-field bridge, covariance comparison, concrete Gaussian
pair laws and canonical signed response separation now also compile. The
signed physical-pressure application is now complete in CoupledMainRootSigned.
The whole initial interval, including negative overlaps, has coefficient 1/8.
The far nonroot inner case now compiles in CoupledMainInnerUniform, with one
positive gap uniform over all inner levels, times, separated overlaps and
volumes of each MIN. Its tolerance is selected before all MIN parameters and
probability field laws. CoupledMainOuterUniform now proves the mirror far
case, including terminal scalar masses above one and k=0. CoupledMainZeroTime
proves the zero-time quadratic penalty with coefficient 1/2 at every level
and realizable overlap. The strict adjacent rearrangement, scalar finite
sorting, paired Gaussian comparison and equality rigidity now compile as
general finite-list results. The actual labelled canonical merge, scalar
regrouping and correction sum now also compile. The concrete one-site
outside-neighbor strictness now compiles for both signs, with the initial
exception retained. The merged overlap path and its signed matrix domain,
constant auxiliary coordinates and zero terminal defect also compile.
The exact driven endpoints, concrete signed covariance columns and raw
matrix correction now compile. The entire zero-mass root prefix is extracted,
and the actual positive suffix masses meet the cascade admissibility API.
The compressed matrix, aggregate standard root columns, exact root/positive
Gaussian laws and concrete canonical finite-volume comparison now compile.
The full positive site recursion is identified with its actual paired list.
The outer zero-mass root expectation and complete site identity now compile.
Exact auxiliary source projection, zero-contribution deletion and Gaussian
transport identify the original physical pressure with its terminal normalization.
The actual i.i.d. field comparison and a pointwise outside-neighbor physical
gap now compile, with the gap chosen before volume and Gaussian realization.
The paired variance modulus and concrete joint time/magnitude continuity
also compile. The actual site identity and continuity now hold at arbitrary
coupling. Every closed split endpoint is covered, and the zero-time scalar
coupling witness is identified with the concrete stationary q-moment.
Fixed canonical trial overlaps bound every realized overlap with the exact
tangent defect and a continuous scalar witness. Compact uniformization now
gives one physical gap on separated outside regions before all original
levels, times, overlaps, volumes and Gaussian laws, including time zero.
The neighboring-boundary strips and initial root exception require the
other trial families before the full main estimate. Later probabilistic
stages and the capstone remain open.

The standalone [analytic library](../Analytic.lean) has checked
proofs for the generic analytic inputs. Its [guide](ANALYTIC.md) records what
they establish, their validation, and how to apply them at each phase below.
The concrete mass modules now consume its mass-transform bounds and
field-integral differentiation theorem. Variance response calculus now also
has concrete operator specializations. The split-array and stationary-moment
bridges for both mass orientations are now proved. Both stationary
profile-coordinate remainders and the scalar critical response gap compile.
The nonroot inner/outer coupling-to-response identification and the associated
one-site critical gains now compile. Their nearby finite-volume main-estimate
applications now compile, with all physical Gaussian-law and terminal
normalization bridges proved. The nonnegative root pressure gain and nearby
root estimate also compile. The whole nonnegative interval and canonical
signed response separation also compile. The actual signed pressure bridge
and whole initial interval now compile in CoupledMainRootSigned. The remaining
main-estimate cases and later probabilistic stages still need work.

## Next task

The requested lower-bound goal is complete. No proof obligation remains in
`ParisiLowerBound.lean`. Future maintenance should preserve its four public
statements and the existing field, profile and covariance assumptions.
The structural refinement also adds the completed capstone and every Parisi
module to the root convenience import. The analytic filename and topic
reorganization is recorded in [the refinement record](#analytic-topic-refinement).
The shared API pass is recorded in [the refinement record](#shared-api-refinement).
The next maintenance priority is the [consolidation backlog](#consolidation-backlog),
following the [milestone review rules](../AGENTS.md#milestone-review-before-a-pr).
Start with existing API comparisons and small corollary replacements, then
migrate consumers before removing redundant objects. Preserve capstone contracts
and validate changed owners and consumers explicitly.

The 2026-10-16 refinement moves the generic translation and concatenation lemmas
to Common and removes the duplicate full-domain measurability proof. The other
backlog items remain open. Keep edits focused on Parisi, allowing the
generic Common/Mathlib moves and necessary consumer changes described in
[AGENTS.md](../AGENTS.md#work-efficiently). The build wrapper lives
at [.parisi-lean.ps1](../.parisi-lean.ps1). It resolves the repository root
from its own location, so the capstone can be built from this directory:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File ./.parisi-lean.ps1 build SpinGlass.Parisi.ParisiLowerBound
```

The historical validation results below are retained. Their displayed wrapper
paths use its current location; validation before the move used the root copy.

The final proof chain is:

- `RemainderLimit` and `RemainderIntegral`: the actual finite remainder,
  Gaussian expectation and time integral converge at fixed weights with
  the profile curvature bound.
- `FixedWeightIdentity`: exact pressure differences on every closed
  interpolation subinterval, with a field- and weight-independent bound.
- `CascadeMarkTransport` and `PairGaussianTransport`: measurable transport
  of all independent marks and their laws, including zero scaling.
- `RemainderLaw`, `RemainderAverage`, `RemainderTimeAverage`: the resulting
  expectation is exactly the physical `parisiGuerraRemainder`; its time
  integrability and all required changes of integration order are proved.
- `PressureWeightAverage`, `PressureFieldAverage`, `PressureDifference`:
  Gaussian integrability at each fixed field and the exact original pressure
  average under only a first field moment. No exponential field moment or
  logarithmic total-weight moment is added.
- `BoundAverage` and `IntegralIdentity`: the bound average is the bracket
  slope, and the original pressure gap equals the remainder integral on
  the entire interval, including both endpoints. Its sign is proved.
- `GapBounds`, `IntegralGronwall`, `LowerComparison`: gap continuity,
  curvature control of the final interval, and a scalar integral Gronwall
  estimate that does not assume continuity of the physical remainder.
- `BoundedLowerBound`: choose the cutoff from curvature and target accuracy,
  choose MIN parameters using the uniform localization tolerance, then choose
  the finite-volume accuracy after the Gronwall constant.
- `ParisiLowerBound`: apply `FieldTruncation` to the bounded nondegenerate
  theorem. The original zero-field reduction and convergence results now
  depend on the completed proof.

Completion validation on 2026-10-13 used Lean 4.34.0-rc2:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File SpinGlass/Parisi/.parisi-lean.ps1 build `
  SpinGlass.Parisi.ParisiLowerBound `
  SpinGlass.Parisi.Coupled.CoupledMainEstimate `
  SpinGlass.Parisi.Interpolation.IntegralIdentity `
  SpinGlass.Parisi.Interpolation.PressureDifference `
  SpinGlass.Parisi.Interpolation.RemainderTimeAverage
```

The build passed with 3794 jobs. An `env lean` audit of all 61 public
completion theorems and all four capstone theorems reports only `propext`,
`Classical.choice`, and `Quot.sound`. The folder scan finds no `sorry`,
`admit`, project axiom or unsafe declaration. `git diff --check` passed.
All source and documentation changes stayed inside Parisi.

## Consolidation backlog

Recheck each candidate against current source, the pinned Mathlib and the
target `main` API before changing it. The paths below were inspected for the
instruction update; equivalence and migration proofs remain work to do.
Record a candidate as resolved only with its replacement or a concrete reason
to retain it, consumer updates, and relevant validation. Do not turn this list
into another permanent layer of wrappers.

### Shared analysis and small duplicate lemmas

- Compare the former `ARISTOTLE.lean`, now `Analytic/`, against the existing
  heat/Cole-Hopf layer. Follow [the analytic reuse guide](ANALYTIC.md#reuse-and-consolidation):
  specialize existing objects, relocate missing general lemmas to Common/Mathlib,
  and remove parallel objects or proofs once consumers use the canonical owner.
Resolved in the [shared API refinement](#shared-api-refinement): generic
Cole-Hopf translations, finite-array concatenation and full-domain derivative
measurability now use the shared Common owners. Do not reintroduce their former
Parisi copies or the separate difference-quotient proof.

The next small comparison is `Heat.heat` in `Analytic/Heat/Basic.lean` against
`integral_comp_add_gaussianReal_zero_var` and
`integral_integral_comp_add_gaussianReal` in the existing Common heat owner.
Check the growth hypotheses and variance domains before replacing the local
zero-time and semigroup proofs; preserve negative-variance clamping.

### One recursion on the closed mass domain

`Minimizer/Compact.lean` defines `closedParisiX₀` through `coleHopfIterate` and
proves `closedParisiX₀_eq_parisiX₀` on admissible strict masses. The original
`parisiX₀` in `SpinGlass/ParisiFunctional.lean` uses `parisiRec`.
Aim for one underlying root value through `coleHopfIterate`, including $m=0$,
with `parisiRec_gaussian_comp_add_sum` as the positive-mass representation bridge.
Preserve the general terminal-function interface and prove each identification
under its actual integrability and mass conditions; the representations need
not agree outside those domains.

Use that root value to consolidate `closedRandomFieldParisiFunctional` with the
existing functional. Preserve the penalty and prove the closed-domain endpoint,
continuity and compact-minimization properties. Migrate uses before removing
the parallel closed/strict stack. Any required change to the owner outside this
folder must remain limited to that consolidation and its consumers.

### One field-law API

Use the probability-law formulation as the primary stack. The existing
`randomFieldParisiFunctional_dirac` in `Field/RandomFieldFunctional.lean`
provides the starting bridge to constant $h$ via $\mu_h=\operatorname{dirac}(h)$.
Review `parisiQ_*`/`randomFieldParisiQ_*` and the `parisiSet`/`parisiInf` and
`randomFieldParisiSet`/`randomFieldParisiInf` families in `ParisiInf.lean`.
Derive constant-field results as corollaries, proving any required moment and
nondegeneracy conditions for the Dirac law; nondegeneracy excludes $h=0$.
Retain the separate zero-field case and the i.i.d. product-coordinate semantics.

Consolidate `_of_convexOn_of_monotone` and related hypothesis combinations around
the weakest useful general theorem. Keep a variant only when it gives a useful
application interface, with a short proof from that theorem.

### Derivatives of the original objects

Review `coleHopfIterateDeriv`/`coleHopfIterateDeriv2` in QVariation/ColeHopf,
`parisiQSuffixDeriv`/`parisiQSuffixDeriv2` in QVariation/Recursion,
`coleHopfMassDeriv` in `Variational/ParisiMassDerivative.lean`, and
`parisiLogCoshTerminalDeriv`/`parisiLogCoshTerminalDeriv2` in QVariation/Terminal.
Expose calculus through `deriv`/`iteratedDeriv` of the actual function and
`HasDerivAt` theorems, with within-set versions where required. Prove that
recursive response formulas equal those derivatives before using them as such.
The terminal formulas $\tanh(h+x)$ and $1-\tanh(h+x)^2$ should be calculation
lemmas on `parisiLogCoshTerminal`, not a second independent calculus API.
Keep an explicit recursive helper only when it serves a proof or application
that the standard derivative interface does not conveniently express.

### Signed tilted conditional square

`Coupled/Derivative/Zero.lean` defines `cascadeTiltTanhSq` by shifted nonnegative
observables and the identity $xy=2(x+1)(y+1)-(x+2)(y+2)+2$.
Use [CascadeTiltMeasure](../../../Common/Mathlib/Probability/PointProcess/CascadeTiltMeasure.lean)
to formulate the general real-valued observable, prove its integrability and
normalization, and express (14.177) and Proposition 14.6.4 directly through it.
Preserve the square of the conditional suffix average followed by the prefix
average; replacing it with an average of the terminal square changes the object.
Prove equality to the current encoding on the admissible domain and migrate
consumers. Keep the nonnegative encoding only where the underlying API requires it.

### Source-level profile and minimizer assumptions

Audit every field of `TalagrandXiCondition` in
`Minimizer/QVariation/Parameters.lean` against (14.101). Prefer standard
regularity predicates when they express the same required scope. A blanket
`ContDiffOn ℝ 3` assumption is not a drop-in replacement: continuity and endpoint
requirements must follow from the source, or be confined to a sufficient-condition
constructor. Keep $\xi''(0)=0$ admissible and covariance PSD separate.

Search for existing model instances, then supply any missing constructors for
nontrivial SK and admissible mixed even p-spin profiles. State coefficient and,
for infinite mixtures, convergence assumptions explicitly and prove the claimed
profile properties. These examples check applicability; they do not alone prove
that the hypothesis bundle matches the book.

Replace the custom minimization comparison in `IsParisiQMinimizer` with Mathlib's
`IsMinOn` on the admissible domain where appropriate. Its present definition also
includes `ParisiQAdmissible qs`; preserve that membership separately or in a
transparent compatibility abbreviation, with a proved equivalence.

### Common insertion statements

Review `parisiRootU`, `parisiRightU` and the corresponding f-functions in
`Variational/ParisiSplitResponse.lean`. Seek one insertion-at-level statement
with root/right results as specializations, extending to the left orientation
where it shares the same mathematics. Account explicitly for the root's zero
mass, empty prefix, fixed endpoints and changes in level count. Do not merge
distinct cases by silently assuming positive mass or two-sided differentiability.

The sections below retain the earlier implementation and validation ledger.

## Shared API refinement

Refinement on 2026-10-16 preserves the four capstone declarations and every
field, profile and covariance assumption. The capstone source is unchanged
from the start of this pass. No new mathematical objects or hypothesis bundles
were introduced.

- `coleHopf_translate` and `coleHopfQ_translate` now belong to
  `ProbabilityTheory` in the Common Gaussian ColeHopf owner. Translation is
  proved directly by associativity at every mass and variance; the existing
  `coleHopf_comp_const_add` specializes it at spatial argument zero.
- `coleHopfIterate_translate` and `coleHopfIterate_append` now belong to
  `ProbabilityTheory` in Common CascadeColeHopf. The array result uses the
  existing list-concatenation theorem. All four former `SpinGlass`
  declarations were removed; existing callers resolve the shared names through
  their owner imports and `open ProbabilityTheory`.
- `measurable_deriv_param` is a specialization of
  `measurable_derivWithin_param` on the full real line, with accumulation
  supplied by `uniqueDiffWithinAt_univ`. The endpoint interfaces are preserved.
- `coleHopfIterate_logCosh_regular` is a theorem with an explicit result type.
  The nonvanishing proof uses the existing derivative translation identity
  directly, removing the second cascade-representation and chain-rule argument.
  The translation theorem keeps its positional mass argument for its callers.
- The touched ColeHopf proofs focus their arithmetic subgoals explicitly and
  use a fixed append simplification. Root instructions now reference the
  current module owners and the completed capstone.

Validation on 2026-10-16 used Lean 4.34.0-rc2. The initial ColeHopf, Terminal
and measurable-derivative leaf builds passed before editing. After refinement,
the Terminal dependency build passed with 3506 jobs, then the complete project,
analytic library and capstone build passed with 3863 jobs:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File SpinGlass/Parisi/.parisi-lean.ps1 build SpinGlass.Parisi.Minimizer.QVariation.Terminal
powershell -NoProfile -ExecutionPolicy Bypass -File SpinGlass/Parisi/.parisi-lean.ps1 build SpinGlass Common SpinGlass.Parisi.Analytic SpinGlass.Parisi.ParisiLowerBound
powershell -NoProfile -ExecutionPolicy Bypass -File SpinGlass/Parisi/.parisi-lean.ps1 env lean .parisi-refinement-audit.lean
git diff --check
rg -n '\b(sorry|admit|axiom|unsafe)\b' SpinGlass/Parisi Common --glob '*.lean'
```

The temporary importing audit checked all fifteen affected public helpers and
the four capstone theorems with `#print axioms`. Every axiom list is contained
in `propext`, `Classical.choice` and `Quot.sound`; no audit errors or `sorryAx`
occur. The source scan has no matches. The five changed Lean owners emit no
warnings; existing warnings in other modules remain. All 536 relative
documentation links and anchors, changed-file whitespace, canonical ownership and
`git diff --check` pass. The capstone source agrees with the session snapshot.
Temporary audit and build-log files were removed after verification.

No mathematical or build blocker remains for this pass. The remaining
consolidation items above have not been claimed complete; the next small task
is the heat zero-variance and semigroup comparison described there.

## Historical structure and proof refinement

The first 2026-10-13 maintenance pass reorganized and simplified the completed proof
without changing its claims. Three agents handled the analytic topics, coupled
estimates, and variational/minimizer proofs; integration preserves the existing
working-tree proof development.

- The former ARISTOTLE.lean became a compatibility umbrella for 24 Mathlib-only Analytic
  owners. All 215 original public source declarations retain their names,
  namespaces and signatures. Three duplicate analytic proofs reuse existing
  envelope and heat results; redundant heat normalization tactics are removed.
- Thirteen concrete consumers import individual analytic owners. The compatibility
  umbrella retains its original Mathlib imports for existing clients.
- Field/FieldMoments.lean owns the unchanged NondegenerateExternalFieldLaw,
  its first-moment lemma and Dirac characterization. One general finite-law
  second-to-first-moment lemma replaces duplicated capstone/stationarity bounds.
- The elementary theta derivative moves unchanged to Parameters. Near-minimum
  selection and parameter continuity no longer import random-field stationarity;
  strict mass extraction requests that dependency explicitly.
- StrictMass shares overlap flattening/deletion and induction descent; Compact
  applies the standard compact minimum theorem directly. Endpoint mass bounds
  use the existing finite-index order API.
- CoupledCompactWitness shares the finite positive minimum construction across
  six consumers. MainTrial shares positive/signed root dispatch in the far and
  off-center estimates, with all original quantifier order and assumptions.
- The complete convenience import covers all 308 modules under Parisi, including
  previously independent auxiliary leaves. README and agent instructions now
  describe current owners; the historical proof ledger below is retained.

Source comparison against the pre-refinement working tree finds all 2,848
existing public-header groups present unchanged. Static checks confirm that
local imports resolve, the graph is acyclic, and no proof holes, project axioms
or unsafe declarations appear under Parisi. Standalone checks of the field
moment owner and the changed coupled/minimizer leaves have passed.

The initial full-coverage build exposed two implicit declaration imports and
three errors in the previously independent cascade product bound. Imports now
name the terminal and analytic owners explicitly. The cascade proof identifies
the empty-coordinate function, uses the current multiplication order lemmas,
and states tail monotonicity and the sliced induction inputs explicitly; its
public theorem statement is unchanged.

Historical validation of that pass on 2026-10-13 used Lean 4.34.0-rc2. The
module targets retain the former module name to record what was built:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File SpinGlass/Parisi/.parisi-lean.ps1 build SpinGlass Common SpinGlass.Parisi.ParisiLowerBound SpinGlass.Parisi.ARISTOTLE SpinGlass.Parisi.Minimizer.Full SpinGlass.Parisi.Variational.ParisiCompactMin
```

The combined repository, leaf and consumer build passed with 3860 jobs. This
covers all 308 Parisi modules, every changed proof owner and the four unchanged
capstone theorems. Existing style and unused-hypothesis linter warnings remain.
A temporary importing Lean file checked all 2,874 public source declarations
with `#print axioms`: 2,859 have axiom lists contained in `propext`,
`Classical.choice` and `Quot.sound`; fifteen depend on no axioms. There were no
audit errors, proof holes, new project axioms or unsafe declarations.

The source-signature comparison, import resolution/cycle/coverage checks,
documentation links, trailing whitespace and `git diff --check` passed.
Temporary build/audit files and the pre-refinement snapshot were removed.
No mathematical or build blocker remains. Future maintenance should start with
a concrete requested change, preserve the public contracts, and validate its
owning leaf and consumers.

## Analytic topic refinement

The follow-up maintenance request replaces the personal source filename with
[Analytic.lean](../Analytic.lean). The umbrella contains imports and module
documentation; definitions and proofs belong to the mathematical topic owners.
Existing declarations, namespaces, theorem statements and assumptions are
preserved. Code using `SpinGlass.Parisi.ARISTOTLE` should import
`SpinGlass.Parisi.Analytic` instead.

Mass definitions, derivatives and bounds are separated under Analytic/Mass.
Gaussian integrability, differentiation, curvature and split responses are
grouped under Analytic/Gaussian. The existing Analytic/Heat sequence is retained.
Generic integral concavity and derivative-to-Lipschitz bounds move to Convexity
and Lipschitz. The resulting 27 topic owners retain all 215 public analytic
declarations.
[ANALYTIC.md](ANALYTIC.md#topic-owners) and [INDEX.md](../INDEX.md) identify the
current declaration owners; all concrete imports are updated accordingly.

The independent source review verifies that all 215 analytic declarations keep
their exact names and namespaces, normalized signatures, and complete proof or
definition bodies, with no additions, omissions or duplicates. All local imports
resolve, the graph is acyclic, and the convenience import reaches all 311 current
Parisi modules. The 27 guide inventory rows match source declaration counts, and
all local documentation links resolve.

The focused Mass.Bounds build passed with 3100 jobs. Direct Lean checks of
Convexity and Lipschitz also passed. The full build completed on 2026-10-14 with
this command from the repository root:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File SpinGlass/Parisi/.parisi-lean.ps1 build SpinGlass Common SpinGlass.Parisi.Analytic SpinGlass.Parisi.ParisiLowerBound
```

The build passed with 3863 jobs. All 311 Parisi modules are reachable and
compiled, including the analytic library, the SpinGlass root and the unchanged
lower-bound capstone. An `env lean` foundation audit on 2026-10-14 checked all
2,874 public source declarations, including the four capstone theorems, and
exited successfully. Of these declarations, 2,859 have axiom lists contained in
`propext`, `Classical.choice` and `Quot.sound`; fifteen depend on no axioms.
There were no audit errors. Original analytic signatures and complete proof or
definition bodies are preserved. The historical builds and axiom audits above
apply to their recorded source state.

## Build wrapper relocation

On 2026-10-14, `.parisi-lean.ps1` moved into this directory. The wrapper resolves
the repository root from its own path and runs Lake there, allowing editing and
build invocations from `SpinGlass/Parisi/` with the existing parent cache.
The folder-only editing scope recorded here applied to that maintenance task;
current consolidation scope is specified in [AGENTS.md](../AGENTS.md#work-efficiently).

Runtime checks passed from both the repository root and the Parisi directory.
The child process used the repository root, and an invalid Lake flag propagated
exit code 1. The capstone build from the Parisi directory passed with 3817 jobs:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File ./.parisi-lean.ps1 build SpinGlass.Parisi.ParisiLowerBound
```

This maintenance change preserves the Lean sources and the earlier proof
validation records. Local documentation links and `git diff --check` passed.

## Localization and finite interpolation record

`parisiOverlapValues` is the exact overlap image and has cardinality at most
N+1. The main estimate and pressure-gap concentration now prove
`exists_uniform_parisiBranchMeetingMass_localization`, with one constant
before accuracy and one eventual volume bound for all times and levels.
The sum of the actual constrained tilted masses is one, and the sum of
the physical masses at level r is exactly `mExt ms (r+1) - mExt ms r`.
`SecondMoment` converts localization to the required physical squared
overlap control and proves the uniform total bound four.

`ProfileRemainder` derives the signed derivative and quadratic convexity
remainder from the preserved profile contract. `LocalizedRemainder`
combines it with the actual masses and full main estimate; no concentration
or localization conclusion is assumed in its final MIN-level theorem.
The remainder is a concrete observable; its infinite-tree derivative
interpretation is still the next bridge.

`PressureLaw` identifies the time-scaled recursion with the original
`hamG` expectation under fixed laws, including both endpoints and zero
variances. `PressureIntegrability` supplies first-moment integrability.
`InitialEndpoint`, `TerminalEndpoint` and `Bracket` identify the actual
initial bracket, terminal i.i.d. free energy and affine correction slope.
`WeightedDerivative` and `WeightedIntegral` supply the exact weighted
Gaussian derivative, its integrated form and a trace bound independent of
the number of states. `TreeRemainder` retains the profile defect in the
tree covariance identity and bounds it by the curvature at one.
`TruncatedDerivative` instantiates these with the actual original Gaussian
tree and normalized finite weights. This last formula has only the original
profile, covariance PSD, admissible overlap and nonzero-weight assumptions.

## Completed concentration interfaces and supporting record

Concentration and truncation continuation on 2026-10-13:
[FieldTruncation.lean](../Field/FieldTruncation.lean) now proves the concrete
bounded-law approximation. Positive clipping preserves nondegeneracy, and
the free-energy and Parisi-infimum errors are bounded by the same scalar
first-moment cost uniformly in volume. Its final theorem is explicitly a
conditional reduction to the bounded nondegenerate site-law lower bound.

The new [Concentration](../Concentration) modules use the actual
`cascadeTilt`, `pairHamG` and Gaussian mark laws. CascadeTiltGap proves
the recursive power inequality and its logarithmic form (14.120).
CascadeTiltContinuity uses the existing cascade Gibbs identity to bound
logarithmic perturbations independently of cascade depth. PairTiltMass
defines the physical constrained tilted mass, proves its positivity for
nonempty constraints, its bound by one and its logarithmic pressure-gap
inequality. PairTiltDisorder proves a joint Hamiltonian perturbation bound,
including root-mark changes, and the coefficient-four disorder bound.
PairTiltFieldConcentration proves, for arbitrary fixed disorder and root
marks and clipped shared fields,
$\mathbb E\exp(s(L-\mathbb E L))\le\exp(8R^2Ns^2)$
for the actual logarithmic tilted mass $L$. This bound is uniform in the
conditioned Gaussian variables and needs no exponential field moment.

Gaussian concentration continuation on 2026-10-13:
[GaussianLipschitz.lean](../Concentration/GaussianLipschitz.lean) extends the
smooth Gaussian theorem to every finite-dimensional Lipschitz observable.
Normalized smooth convolution preserves the Lipschitz constant, dominated
convergence identifies the means, and Fatou passes the MGF bound to the
limit. No derivative of the final observable is assumed.

[PairTiltGaussianConcentration.lean](../Concentration/PairTiltGaussianConcentration.lean)
identifies the actual branch coefficient, including the interaction and root
marks. PairGaussianCoefficients proves its square-root volume bound.
GaussianCoordinates constructs the covariance square root; GaussianCoordinateLaw
proves the exact interaction/root product law and independence. The final
physical result is
`hasSubgaussianMGF_pairHamLogTiltMass_root_variance` in
[PairTiltRootVariance.lean](../Concentration/PairTiltRootVariance.lean).
For $S_{\sigma\sigma}\le ND$ and $\sum_jK_{0,lj}^2\le d$, it proves
$\mathbb E\exp(s(L-\mathbb E L))\le\exp(16N(D+v_0d)s^2)$
under the actual centered interaction law with covariance $S$ and independent
root marks of variance $v_0$. It includes $v_0=0$, singular $S$, and zero
positive levels. Its variance proxy is independent of the external field
and the number of cascade levels. Positive masses are strictly increasing
and strictly below one, as required by the cascade Gibbs identity.

Joint concentration continuation on 2026-10-13:
[ProductSubGaussian.lean](../Concentration/ProductSubGaussian.lean) proves the
conditional combination, including joint exponential integrability. Uniform
coordinate oscillations pass to the Gaussian-averaged mean. The actual result
in [PairTiltCombinedConcentration.lean](../Concentration/PairTiltCombinedConcentration.lean)
is integrability and variance proxy $N(32(D+v_0d)+16R^2)$ under the full
interaction/root/i.i.d.-field law. Joint continuity includes all field coordinates.

[PairTiltPressureGap.lean](../Concentration/PairTiltPressureGap.lean) then proves
that an averaged unnormalized pressure difference at most $-\varepsilon N$
gives the actual tilted-mass bound
$\exp(-b\varepsilon N/2)+\exp(-(b\varepsilon)^2N/(8C))$,
where $0<b\le1$, $b\le m_i$ for every positive mass, and
$C=1+32(D+v_0d)+16R^2$. Pressure-difference integrability follows from
$L\le b(J_c-J_1)\le0$ and integrability of $L$; it is not an extra assumption.
[PairTiltBoundedField.lean](../Concentration/PairTiltBoundedField.lean) removes
clipping for any site law satisfying $|h|\le R$ almost surely and states both
results on the original field coordinates. The finite-second-moment target
still uses the separate uniform truncation reduction.

Physical concentration continuation on 2026-10-13:
[ParisiTiltParameters.lean](../Concentration/ParisiTiltParameters.lean) discharges
the original covariance diagonal, root variance, row norm and positive mass
lower bounds. ParisiTiltConcentration applies the joint concentration estimate
to the original halved masses and common-prefix factors, uniformly in time,
volume, meeting level and overlap. PairBranchFactorization identifies the
unconstrained pair recursion with the square of the actual single-copy recursion.
PairPressureIntegrability proves both log pressures separately integrable from
a first field moment. ParisiPressureIdentification proves the exact gap identity
$\int(J_c-J_1)=N(\Psi_r-2\varphi_N)$, where `parisiInterpolationPressure`
is the actual single-copy recursion under the time-scaled Gaussian law.

PairTiltBranchIdentity transports the constrained numerator and tilt to the
actual common-prefix pair law. CascadePairBounds supplies bounded normalized
prefix sums; PairBranchMeeting turns their difference into an ordinary
integral and proves its exact mass-increment times tilted-mass identity.
[ParisiBranchConcentration.lean](../Concentration/ParisiBranchConcentration.lean)
then proves `exists_uniform_parisiBranchMeetingMass_exponential_bound`:
for a bounded probability site law and each positive pressure gap, one $c>0$
works before all volumes, times, levels and realizable overlaps, giving
$\mathbb E\langle 1_{R=u,\,\mathrm{meeting}=r}\rangle\le2\exp(-cN)$.
Unrealizable overlaps have zero mass. This is the bounded-field version of
Proposition 14.5.8 on the actual canonical Gaussian and tree laws; no MGF,
integrability, coefficient-norm or branch-identity hypotheses remain.

Next combine this bound with CoupledMainEstimate, enumerate the finite overlap
values, and sum to prove uniform localization. Keep the localization constant
independent of its auxiliary tolerance. Connect `parisiInterpolationPressure`
and these time-scaled tree averages to the existing Guerra interpolation and
its derivative remainder; the pointwise `unscaledHamG_interpolation_eq_hamG`
is available, but the full joint-law and derivative identification remains.
Then prove the bounded-law lower interpolation and endpoint comparison before
using FieldTruncation. The nondegenerate capstone remains open.

Validation of the joint concentration continuation: the bounded-field,
main-estimate and capstone build passed with 3741 jobs. All 17 supporting
theorems in the four new owners and the two continuity/field owners pass
`#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof holes in these modules; the only `sorry` in Parisi remains
in the unchanged nondegenerate capstone. `git diff --check` passed.

The combined root-variance, field-concentration, main-estimate and capstone
build passed with 3737 jobs. All 32 theorems in the seven new Gaussian
concentration owners were audited using `#print axioms` and use only
`propext`, `Classical.choice`, and `Quot.sound`. No new proof holes remain.
The original capstone still depends on `sorryAx`; `git diff --check` passed.

The combined concentration-input, truncation, signed-root and capstone
consumer build passed with 3664 jobs. All 25 supporting theorems in the
five concentration owners and FieldTruncation were audited with
`#print axioms`; each uses only `propext`, `Classical.choice`, and
`Quot.sound`. The original capstone still depends on `sorryAx`.

The full main estimate is now proved in
[CoupledMainEstimate.lean](../Coupled/CoupledMainEstimate.lean).
`exists_uniform_randomFieldParisiAuxPairPressure_main_estimate` chooses a
positive MIN tolerance before all parameters, then one positive constant
uniform over every volume, time, original level, realizable overlap and
Gaussian law. It includes every neighboring boundary and both root signs.
The next mathematical stage is Proposition 14.5.8: instantiate the weighted
cascade product, its logarithmic pressure-gap inequality and Gaussian
fluctuation bound, then combine the actual field fluctuations. Localization,
lower interpolation and the nondegenerate capstone remain open.

Validation on 2026-10-13: the main-estimate, full-MIN and capstone consumer
build passed with 3712 jobs. All 38 public supporting theorems in the eight
new free-trial, positive-root and main-estimate owners were audited with
`#print axioms`; each uses only `propext`, `Classical.choice`, and `Quot.sound`.
The capstone retains its original hole. The temporary audit was removed.

Signed-root fixed-trial continuation verified on 2026-10-13:
[CoupledRootSignedContinuity.lean](../Coupled/CoupledRootSignedContinuity.lean)
identifies the actual product root law with two genuine zero-mass paired
expectations and the positive independent suffix, and proves arbitrary-coupling
time continuity. [CoupledRootSignedTrialComparison.lean](../Coupled/CoupledRootSignedTrialComparison.lean)
proves the exact fixed-trial physical comparison at every realized constraint,
its i.i.d. field average, and a globally continuous scalar trial gap.
`exists_parisiRootSignedTrialGap_pos_of_response_ne_zero` selects a strictly
positive inserted mass using the proved mass limit.
`exists_uniform_parisiRootSignedTrial_positive_gap` packages these as
`ParisiRootSignedTrial` witnesses on the entire closed negative initial
interval, with the MIN tolerance preceding all parameters. No derivative,
Gaussian law, pressure gap or field exponential moment is assumed.

Validation: the combined build below passed with 3709 jobs. All 15 supporting
theorems in CoupledOverlapTangentDefect, CoupledRootSignedContinuity and
CoupledRootSignedTrialComparison were audited using `#print axioms`; each
uses only `propext`, `Classical.choice`, and `Quot.sound`. The capstone still
uses `sorryAx` and retains its original hole. `git diff --check` passed.
The initial duplicate inner/outer trial files from this session were removed
after the concurrently added CoupledInnerFreeTrialComparison,
CoupledOuterFreeTrialComparison and CoupledFreeTrialWitness built successfully.
Those files are the free-mass trial owners.

```text
lake build SpinGlass.Parisi.Coupled.CoupledRootSignedTrialComparison SpinGlass.Parisi.Coupled.CoupledCanonicalTrialComparison SpinGlass.Parisi.Coupled.CoupledMainOutsideUniform SpinGlass.Parisi.Coupled.CoupledFreeTrialWitness SpinGlass.Parisi.Coupled.CoupledRootTrialComparison SpinGlass.Parisi.ParisiLowerBound
```

The signed-root bridge is consumed by the completed full compact witness
family in CoupledMainTrial through CoupledMainEstimate. Concentration
transfer, localization and lower interpolation remain open.

The signed-root integration was rechecked on 2026-10-13 after the concurrent
main-estimate changes. Building CoupledRootSignedTrialComparison,
CoupledMainEstimate and ParisiLowerBound together passed with 3712 jobs.
The 15 signed-root/tangent-defect theorems and the final main-estimate theorem
all use only `propext`, `Classical.choice`, and `Quot.sound`. There is no
remaining signed-root proof obligation in this interface. The original
nondegenerate lower-bound theorem still depends on `sorryAx`.

The fixed-trial comparisons now cover the free inner/outer masses and the
positive signed-root insertion. Assemble the full compact main estimate
with a tolerance preceding every MIN. The canonical outside trial family
already has its exact physical comparison, scalar continuity and compact
uniform gap on separated regions, including time zero.
The whole initial interval in Proposition 14.8.3 now compiles in
[CoupledMainRootSigned.lean](../Coupled/CoupledMainRootSigned.lean).
`exists_uniform_randomFieldParisiAuxPairPressure_root_gap` gives coefficient
1/8 for every realizable $|u|\le q_1$, with the MIN tolerance selected before
parameters, volume and time. Both signs use the original physical pressure.
The nearby nonroot/outer estimates compile in
[CoupledMainNear.lean](../Coupled/CoupledMainNear.lean).

The field-law approximation bridge completed before this session was
restricted to signed roots is in
[FieldLawContinuity.lean](../Field/FieldLawContinuity.lean). It bounds changes
of finite-volume pressure, the Parisi functional and the Parisi infimum by
the expected absolute difference in a common scalar coupling, with constant
one. Its leaf build passed; truncation and concentration are still separate
tasks.
The final signed-root, canonical-trial, field-law and capstone consumer build
passed with 3671 jobs. A combined audit of the 15 signed-root/tangent-defect
theorems and seven field-law theorems found only standard Lean foundations;
the original capstone still depends on `sorryAx`.

The adjacent Cole-Hopf rearrangement in Lemma 14.10.5 now compiles in
[ParisiColeHopfSwap.lean](../Variational/ParisiColeHopfSwap.lean), including
strictness for the actual recursive log-cosh suffix, inner mass zero and
zero variances. [ParisiColeHopfRearrangement.lean](../Variational/ParisiColeHopfRearrangement.lean)
proves finite-list sorting, strictness at active inversions, field-averaged
equality rigidity and the exact original full-list comparator.
[CoupledPairRecursion.lean](../Coupled/CoupledPairRecursion.lean) proves the
actual common/antisymmetric/independent finite Gaussian comparison and its
field average. [CoupledPairGap.lean](../Coupled/CoupledPairGap.lean) excludes
an earlier nonzero independent mark before a positive correlated mark.
[CoupledOppositeColeHopf.lean](../Coupled/CoupledOppositeColeHopf.lean) supplies
the opposite-direction root exclusion, allowing both root masses to be zero.
Their canonical physical application now compiles at each fixed interior
time and overlap; uniformity over time and separated overlaps is still required.

The labelled canonical lists are now constructed in
[CoupledCanonicalPieces.lean](../Coupled/CoupledCanonicalPieces.lean).
Physical sorting retains both source lists in order, including tied root
masses, by [CoupledCanonicalOrder.lean](../Coupled/CoupledCanonicalOrder.lean).
The exact interval variance sums and scalar regrouping (14.376) now compile
in [CoupledCanonicalScalar.lean](../Coupled/CoupledCanonicalScalar.lean), giving
the original full Parisi comparator. The labelled correction sum equals the
old correction in [CoupledCanonicalCorrection.lean](../Coupled/CoupledCanonicalCorrection.lean).
The construction allows terminal splits and retains the additional mass-zero
expectation when splitting the root interval.

The merged overlap path is now constructed in
[CoupledCanonicalPath.lean](../Coupled/CoupledCanonicalPath.lean).
`parisiCanonicalMergedPieces_filter_driven` recovers the exact driven source
list, and `parisiCanonicalOverlapPath_step` identifies each actual increment.
The path is monotone in [0,1], its signed matrix path is in [-1,1], auxiliary
coordinates remain constant, and the terminal diagonal defect is zero.

These endpoints now compile in
[CoupledCanonicalEndpoints.lean](../Coupled/CoupledCanonicalEndpoints.lean).
`parisiCanonicalOverlapPath_profile_step` identifies every labelled profile
increment with the actual path. CoupledCanonicalCovariance supplies the actual
driven/auxiliary variances and Gaussian factors, with
`parisiCanonicalDrivenVariance_mul_gram` proving the signed covariance
increments even at zero variance. CoupledCanonicalLevelSum proves the full
matrix correction and its raw `coupledLevelSum` identity. The raw array still
contains zero-mass expectations and cannot be used with the positive-mass
cascade API.

[CoupledCanonicalRootCompression.lean](../Coupled/CoupledCanonicalRootCompression.lean)
extracts the entire zero-mass prefix and its positive suffix from the actual
stable merge. It proves that the split-root independent expectation belongs
to that prefix, and that the concrete suffix masses are positive, monotone
and at most one. Deleting all root correction terms preserves the old
correction.

The compressed matrix API now compiles in
[CoupledCanonicalCompressedPath.lean](../Coupled/CoupledCanonicalCompressedPath.lean).
It identifies every suffix piece with its raw index, transfers its covariance,
terminal defect and correction, and telescopes the entire root covariance.
[CoupledCanonicalGaussianColumns.lean](../Coupled/CoupledCanonicalGaussianColumns.lean)
constructs disjoint actual driven/auxiliary columns with standard Gaussian
laws and proves their exact root and positive joint-law identities, including
degenerate variances. CoupledCanonicalComparison instantiates the concrete
finite-volume bound, with every covariance, tangent, support, mass and
correction input discharged. CoupledCanonicalPressure now identifies its
pressure with the original auxiliary pressure plus the terminal variance.

CoupledPairGaussianLayer proves the exact Gaussian integral identities for
positive masses and genuine zero-mass expectations in all three paired kinds.
CoupledPairGaussianRecursion identifies the entire finite positive-mass
cascade and Parisi recursion with the actual paired iterate.
[CoupledCanonicalSiteRecursion.lean](../Coupled/CoupledCanonicalSiteRecursion.lean)
uses the proved joint laws to specialize this identity to the actual canonical
standard-coordinate positive suffix, for every separately unit-Lipschitz
terminal. No covariance or recursion identity is assumed.

These bridges now compile in CoupledPairGaussianExpectation,
CoupledCanonicalRootRecursion, CoupledCanonicalAuxiliaryProjection,
CoupledCascadeListDeletion, CoupledCanonicalAuxiliaryTransport,
CoupledCanonicalPressure and CoupledCanonicalFieldComparison.
`exists_randomFieldParisiAuxPairPressure_outside_point_gap` in
[CoupledMainOutside.lean](../Coupled/CoupledMainOutside.lean) chooses the
physical gap before every volume and Gaussian probability realization,
at each fixed interior time and outside overlap. Its compact uniform
extension now compiles in CoupledMainOutsideCompact and CoupledMainOutsideUniform,
including time zero and a finite minimum over all original levels.

CoupledPairVarianceContinuity proves a field-uniform variance modulus for
every separately unit-Lipschitz terminal and all three paired layer kinds,
including mass zero. Its field-average continuity specializes in
[CoupledCanonicalContinuity.lean](../Coupled/CoupledCanonicalContinuity.lean)
to the actual canonical time/magnitude family at each fixed split.

CoupledPairTerminal proves the actual terminal's separate unit Lipschitz
bounds at every coupling, and CoupledCanonicalCoupling proves its complete
site identity and continuity. CoupledCanonicalClosedGap uses the preceding
driven interval when the split-left variance vanishes, so every closed
split is covered. CoupledCanonicalZeroTime deletes all driven identity
operators and recovers the actual old auxiliary law at every coupling.
Its scalar slope is the original q-moment, and its coupling gap is at
least $(u-q_r)^2/2$ at the concrete coupling $u-q_r$.

[CoupledCanonicalTrialComparison.lean](../Coupled/CoupledCanonicalTrialComparison.lean)
separates a fixed trial overlap $s$ from the realized overlap $u$ in
`coupled_bound'_of_monotone`. The terminal defect is exactly
$t(\xi(u)-\xi(s)-(u-s)\xi'(s))$. The physical auxiliary pressure is independent
of the trial; this follows from the already proved generic constrained
partition transport. The resulting `parisiCanonicalTrialGap` is continuous
in time and realized overlap on the whole plane. No continuity of the
constrained finite-volume pressure is asserted or assumed.

[CoupledMainOutsideUniform.lean](../Coupled/CoupledMainOutsideUniform.lean)
proves `exists_uniform_randomFieldParisiAuxPairPressure_outside_separated_gap`.
For each fixed q-minimum and positive separation, one positive gap is chosen
before every original level, time up to the cutoff, separated outside overlap,
volume and Gaussian realization. The initial root strip and neighboring
boundaries remain explicit restrictions; this is not the full main estimate.

The next smallest consumer-ready bridge is the same fixed-trial comparison
for a free inner mass: hold its admissible trial overlap and positive mass
fixed while the realized constraint varies. Add the same exact terminal
tangent defect, retain its already proved mass correction, and prove the
original auxiliary-pressure identity under the realized constraint.
Do the mirror free outer mass, retaining terminal scalar masses above one
while the actual coupled masses stay at most one. Then do the positive
signed-root insertion, with its actual common/antisymmetric root product law.
Use CoupledGaussianSiteContinuity for the actual two-column free-mass site
values at every fixed coupling; root product expectations can use the
proved paired terminal and finite Gaussian expectation interfaces.

Choose concrete continuous trial witnesses from the existing response
or free-mass derivative gains at every remaining point, including the
neighboring boundaries and the signed initial exception. For a root witness,
use the proved positive-insertion approximation and zero-mass limit; do not
apply the positive cascade at mass zero. A finite cover of the full compact
far region $|u-q_r|\ge\rho$, $0\le t\le t_0$ then gives a uniform gap before
volume. Combine it with the already proved nearby quadratic and complete
root estimates, keeping the MIN tolerance before all parameter choices.
The reference argument is printed page 419, following Propositions
14.8.6 and 14.8.7; its upper semicontinuous variational bound is represented
here by the infimum of continuous scalar trial bounds.

The one-site strictness task is complete. CoupledMixedMassGap proves strictness
from actual mixed-mass witnesses, and CoupledCanonicalMagnitudeGap instantiates
these with the labelled pieces, including zero overlap and a zero split-right
variance. CoupledCanonicalRootPrefix proves that the common auxiliary root
and signed driven root are consecutive in the actual stable merge.
[CoupledCanonicalSignedGap.lean](../Coupled/CoupledCanonicalSignedGap.lean)
uses these two nonzero directions and an actual positive correlated tail
piece to prove the negative-overlap case. Its
`exists_randomFieldPairColeHopfListValue_parisiCanonical_outside_gap` rules
out equality in $Y_0\le2X_0$ outside neighboring overlaps, retaining exactly
the initial exception handled by Proposition 14.8.3. CoupledMainOutside
now applies this strictness to the actual physical pressure through proved
root, auxiliary-law, terminal-normalization and i.i.d. field bridges.
Read printed pages 428-438 only as needed for that construction.
Use continuous scalar trial witnesses to obtain a uniform gap independently
of volume. CoupledCanonicalZeroTime now supplies the actual scalar witness
at the zero-time boundary; CoupledMainOutsideCompact already includes it.
CoupledCompactWitness handles an empty region as well. Combine with the
nearby, complete root and far inner/outer estimates for the full theorem.
Keep the finite second external-field moment contract; no exponential field
moment, assumed coupling derivative or final pressure gap is allowed.

The signed root continuation now includes all required concrete bridges:
conditional and averaged product-gradient slope, normalized Gaussian law,
zero-mass response identification, zero value, Taylor gain, signed covariance
and reflected tangents, exact correction, physical auxiliary normalization,
finite-volume comparison and i.i.d. product-coordinate field average.
There is no remaining signed-root proof task.

The root positive inserted-mass limit is already complete:
[CoupledRootMassLimit.lean](../Coupled/CoupledRootMassLimit.lean) proves actual
value and squared-gradient continuity at zero;
[CoupledRootGain.lean](../Coupled/CoupledRootGain.lean) identifies its one-site
value, slope and gain;
[CoupledRootVariance.lean](../Coupled/CoupledRootVariance.lean) supplies the
nonnegative-overlap covariance witnesses, total laws, exact theta correction
and deterministic auxiliary deletion;
[CoupledRootComparison.lean](../Coupled/CoupledRootComparison.lean) proves the
finite-volume and i.i.d. field comparisons. The physical pressure is exactly
independent of every positive inserted mass. CoupledMainRoot takes its actual
zero-mass limit on the right side. Do not reapply `cascadeRec` at mass zero:
its operation there is not the Gaussian expectation used by `coleHopf`.

The far inner/outer and zero-time cases in Propositions 14.8.2, 14.8.5 and
14.8.7 are complete. Finish the canonical outside-neighbor application in
Proposition 14.8.6, and assemble the full uniform main estimate before
concentration, field-fluctuation transfer, localization
and lower interpolation. The compiled coordinate field bound supplies
integrability; it does not establish concentration for a non-Gaussian site law.

The completed mirror curvature tolerance already includes the terminal index:
`exists_uniform_parisi_outer_second_moment_curvature_tolerance` reuses the
old root/nonroot tolerance through the proved initial second-moment identity.
The exact mirror endpoint second derivative is
`derivWithin_derivWithin_parisiLeftf_left_endpoint_of_isMin`, with value
$\xi''(q_L)(\xi''(q_L)M_2(0)-1)$.
Use these and the compiled mirror quadratic remainder in the coupled
main-estimate cases. Treat any remaining terminal endpoint comparison separately: matching
mass one is not a freely varied interior coordinate of the old functional,
so its derivative must not be set to zero by mass stationarity.
Do not add a uniform third-profile-derivative bound, assume a two-sided
variance derivative at a clamped zero, or apply fixed-level minimality across
split dimensions.

The completed mirror profile declarations are
`abs_parisi_outer_variance_sub_linear_le`,
`abs_parisi_outer_profile_correction_sub_quadratic_le`, and
`TalagrandXiCondition.exists_uniform_stationary_outer_response_overlap_radius`
in [ParisiProfileRemainder.lean](../Variational/ParisiProfileRemainder.lean).
The actual consumer is `exists_uniform_parisi_outer_f_overlap_quadratic_radius`
in ParisiOverlapCurvature. The expansion is at q_L; its coefficient is
$\xi''(q_L)(\xi''(q_L)M_2(0)-1)/2$. Both orientations now have first-moment
quadratic variance remainders with coefficient 146 in ParisiCriticalResponse.

The completed moment and stationary endpoint declarations in
[ParisiOuterEndpoints.lean](../Variational/ParisiOuterEndpoints.lean) are
`parisiLeftUSpatialMoment_one_zero_eq_randomFieldParisiQMoment`,
`parisiLeftUSpatialMoment_first_zero_eq_parisiRootUSpatialMoment`,
`parisiLeftUSpatialMoment_succ_zero_eq_parisiRightUSpatialMoment`,
`hasDerivWithinAt_parisiLeftU_zero_of_isMin`,
`hasDerivWithinAt_parisiLeftf_left_endpoint_of_isMin`, and
`parisiLeftf_right_endpoint_eq_zero_of_isMinOn` (nonterminal indices only).
The actual signed final-coordinate transport is
`integral_cascadeTiltMeasure_gaussian_snoc` in
[ParisiCascadeTransport.lean](../Variational/ParisiCascadeTransport.lean).
`abs_parisiLeftUSpatialMoment_two_sub_le` in ParisiMomentDissipation and
`abs_parisiLeftf_sub_variance_quadratic_le_of_isMin` in ParisiVarianceTaylor
retain the coefficient 146 and all admissible variance endpoints.

The completed mirror declarations are
`closedRandomFieldParisiFunctional_split_left_lower_mass`,
`closedRandomFieldParisiFunctional_split_left_matching_le_lower_of_isMinOn`,
`exists_uniform_splitParisiLeftMassDeriv_upper_bound`, and
`exists_uniform_parisiLeftf_upper_bound` in
[ParisiQuantitativeMass.lean](../Variational/ParisiQuantitativeMass.lean).
The last gives $f_{\mathrm{left}}\le4\sqrt{M\varepsilon}$ with M selected
from ξ before the law, levels, parameters and tolerance. The actual recursion
bridge is `closedParisiX₀_split_left_eq` and the derivative bridge is
`splitParisiLeftMassDeriv_eq_U` in
[ParisiOuterSplitResponse.lean](../Variational/ParisiOuterSplitResponse.lean).
The matched-layer complement and its full prefix/field calculus are in
[ParisiOuterMassResponse.lean](../Variational/ParisiOuterMassResponse.lean).

The profile and curvature continuation completed
`exists_uniform_parisi_f_overlap_quadratic_radius`,
`exists_uniform_parisi_endpoint_curvature_tolerance`, and
`exists_uniform_parisi_second_moment_curvature_tolerance` in
[ParisiOverlapCurvature.lean](../Variational/ParisiOverlapCurvature.lean), using
[ParisiProfileRemainder.lean](../Variational/ParisiProfileRemainder.lean).
For each κ>0, the last theorem selects ε>0 before k, masses and overlaps and
gives $\xi''(q_r)M_{r,2}\le1+\kappa$ for the actual root/nonroot moments of
every eligible MIN. Both interval-length cases are proved. The profile
corrections have uniform small quadratic error on compact intervals separated
from zero. The sixth-root rate in (14.283) and cubic profile rate in (14.284)
are not asserted; later near-overlap proofs should use this tolerance theorem.

Verification on 2026-10-12: the following command passed with 3589 jobs:

```text
lake build SpinGlass.Parisi.Variational.ParisiProfileRemainder SpinGlass.Parisi.Variational.ParisiOverlapCurvature SpinGlass.Parisi.Variational.ParisiCriticalResponse SpinGlass.Parisi.Coupled.CoupledFieldTaylor SpinGlass.Parisi.Coupled.CoupledSecondDeriv SpinGlass.Parisi.Coupled.Derivative.Zero SpinGlass.Parisi.Variational.ParisiVarianceTaylor SpinGlass.Parisi.Variational.ParisiQuantitativeMass SpinGlass.Parisi.ParisiLowerBound
```

A temporary `lake env lean` axiom audit of all 130 public theorems in the
profile-remainder, overlap-curvature, quantitative-mass, moment-bounds,
moment-dissipation, variance-Taylor, cascade-transport, outer-endpoint and two
outer-response, critical-response and coupled-field owners passed with
only `propext`, `Classical.choice`, and `Quot.sound`. The separate capstone
audit still reports `sorryAx`. No build blocker remains. The lower-bound
capstone still has its original hole.
`git diff --check` and local documentation-link checks passed. The proof-hole
scan of SpinGlass/Parisi and Common still finds only `ParisiLowerBound.lean:44`.

## Completed arbitrary coupling, zero-time witness and compact outside regions

Verified on 2026-10-13 with Lean 4.34.0-rc2:

```text
lake build SpinGlass.Parisi.Coupled.CoupledMainOutsideUniform SpinGlass.Parisi.Coupled.CoupledGaussianSiteContinuity SpinGlass.Parisi.Coupled.CoupledMainOutside SpinGlass.Parisi.Coupled.CoupledMainNear SpinGlass.Parisi.Coupled.CoupledMainRootSigned SpinGlass.Parisi.Coupled.CoupledMainInnerUniform SpinGlass.Parisi.Coupled.CoupledMainOuterUniform SpinGlass.Parisi.Coupled.CoupledMainZeroTime SpinGlass.Parisi.Minimizer.Full SpinGlass.Parisi.ParisiLowerBound
```

The combined leaf/consumer build passed with 3703 jobs. A subsequent
GaussianSiteContinuity leaf build passed after removing unused simp arguments.
Eleven new owners prove 45 supporting theorems: seven in CoupledPairTerminal,
five in CoupledCanonicalCoupling, four in CoupledCanonicalClosedGap,
three in CoupledCanonicalCouplingComparison, one in CoupledPairGaussianSite,
two in CoupledPairListDeletion, six in CoupledCanonicalZeroTime,
seven in CoupledCanonicalTrialComparison, four in CoupledMainOutsideCompact,
three in CoupledMainOutsideUniform and three in CoupledGaussianSiteContinuity.

The complete canonical site value and its variance continuity now hold at
every coupling, with the actual terminal's separate unit Lipschitz bounds.
Strictness holds at every closed split, replacing a zero split-left mark
by the preceding actual driven interval. Zero-variance paired operators can
be deleted even at mass zero; at time zero this recovers the original
auxiliary site law at every coupling. Its concrete coupling slope is the
original stationary q-moment, giving the quadratic scalar witness.

The fixed-trial canonical comparison holds at every realized overlap with
its explicit tangent defect, and its scalar gap is globally continuous in
time and realized overlap. A finite cover therefore gives one physical
gap on compact outside regions excluding the stated initial exception.
A finite minimum over the original levels gives a single positive gap on
all concrete separated outside regions, before times, overlaps, volumes
and Gaussian realizations. The zero-time boundary and k=0 are included.
This theorem retains the neighboring-boundary and initial-root strips;
fixed free-mass and root trials are still needed for the full main estimate.
The actual common-prefix two-column Gaussian site law has arbitrary-coupling
continuity under continuous root and positive variances and only a finite
first field moment, providing the next free-mass trial interface.

A temporary `lake env lean` audit of all 45 supporting theorems reports
only `propext`, `Classical.choice` and `Quot.sound`, or a subset. The unchanged
capstone still reports `sorryAx`. The Parisi/Common proof-hole scan finds
only `ParisiLowerBound.lean:44`; that capstone has no diff. `git diff --check`,
all local documentation links, all eleven new declaration-owner entries and
new-source whitespace, namespace and proof-hole checks passed. Temporary
audit files were removed. There is no build blocker. The next concrete
bridge is the free-inner fixed-trial physical comparison described above;
mirror and signed-root trial bounds, full compact main-estimate assembly,
concentration, field-fluctuation transfer, localization and lower interpolation
remain open. All source and documentation edits stayed inside Parisi.

## Completed root recursion, original pressure and paired continuity

Verified on 2026-10-13 with Lean 4.34.0-rc2:

```text
lake build SpinGlass.Parisi.Coupled.CoupledCanonicalContinuity SpinGlass.Parisi.Coupled.CoupledMainOutside SpinGlass.Parisi.Coupled.CoupledMainNear SpinGlass.Parisi.Coupled.CoupledMainRootSigned SpinGlass.Parisi.Coupled.CoupledMainInnerUniform SpinGlass.Parisi.Coupled.CoupledMainOuterUniform SpinGlass.Parisi.Coupled.CoupledMainZeroTime SpinGlass.Parisi.Minimizer.Full SpinGlass.Parisi.ParisiLowerBound
```

The combined leaf/consumer build passed with 3692 jobs. Ten new owners prove
54 supporting theorems: ten in CoupledPairGaussianExpectation, three in
CoupledCanonicalRootRecursion, twelve in CoupledCanonicalAuxiliaryProjection,
four in CoupledCascadeListDeletion, seven in CoupledCanonicalAuxiliaryTransport,
four in CoupledCanonicalPressure, two in CoupledCanonicalFieldComparison,
one in CoupledMainOutside, nine in CoupledPairVarianceContinuity and two in
CoupledCanonicalContinuity.

Integrability and Fubini identify every actual zero-mass root expectation,
including the extra independent mark of a root split. The actual complete
zero-coupling site value equals the canonical paired list. Filtering the
root and suffix recovers exactly the original auxiliary source. Probability
layers with zero additive contributions can all be deleted in order; a
dependent tuple/list identity retains their exact finite coordinates.
Projection and square-root rescaling give the actual surviving Gaussian
laws, including zero variances. The canonical physical pressure therefore
equals the old auxiliary pressure plus its terminal mass-one variance.

The field comparison uses the actual independent site coordinates and only
a finite first moment. At each fixed interior time and outside overlap,
the actual pressure has one positive gap chosen before all volumes and
Gaussian realizations. This is a pointwise physical application of the
strictness in Proposition 14.8.6, not its full compact uniformization.
The paired variance modulus is uniform in both fields, propagates through
every actual finite list and survives the first-moment field average.
The concrete canonical value is jointly continuous in time and magnitude
at each fixed mass array and split, including clamped zero variances.

A temporary `lake env lean` audit of all 54 supporting theorems reports
only `propext`, `Classical.choice` and `Quot.sound`, or a subset. The unchanged
capstone still reports `sorryAx`; the Parisi/Common proof-hole scan finds
only `ParisiLowerBound.lean:44`. `git diff --check`, local documentation links,
all ten new declaration-owner entries and new-source whitespace checks passed.
The temporary audit files were removed. No build blocker remains. All source and
documentation edits stayed inside Parisi. Compact uniformization, its
zero-time coupling witness, full main-estimate assembly, concentration,
field-fluctuation transfer, localization and lower interpolation remain open.
At that verification the next bridge was the nonzero-coupling terminal site
identity and continuity; the preceding completion record now proves both.

## Completed compressed comparison and positive site recursion

Verified on 2026-10-13 with Lean 4.34.0-rc2:

```text
lake build SpinGlass.Parisi.Coupled.CoupledCanonicalSiteRecursion SpinGlass.Parisi.Coupled.CoupledCanonicalComparison SpinGlass.Parisi.Coupled.CoupledCanonicalSignedGap SpinGlass.Parisi.Coupled.CoupledMainNear SpinGlass.Parisi.Coupled.CoupledMainRootSigned SpinGlass.Parisi.Coupled.CoupledMainInnerUniform SpinGlass.Parisi.Coupled.CoupledMainOuterUniform SpinGlass.Parisi.Coupled.CoupledMainZeroTime SpinGlass.Parisi.Minimizer.Full SpinGlass.Parisi.ParisiLowerBound
```

The combined leaf/consumer build passed with 3682 jobs. Six new owners prove
42 supporting theorems: 12 in CoupledCanonicalCompressedPath, 14 in
CoupledCanonicalGaussianColumns, 1 in CoupledCanonicalComparison, 12 in
CoupledPairGaussianLayer, 2 in CoupledPairGaussianRecursion and 1 in
CoupledCanonicalSiteRecursion. The concrete compressed path handles the
entire zero-mass prefix; its positive array and aggregate root satisfy the
proved covariance and correction identities. Disjoint standard Gaussian
columns have exactly the actual root and positive joint laws, including
zero variances. These instantiate the concrete finite-volume bound with no
supplied covariance, support, correction or pressure comparison hypotheses.

All three Gaussian layer kinds have exact positive exponential and zero-mass
expectation identities. The actual finite positive-mass cascade and Parisi
recursion equal the concrete paired iterate. The canonical site theorem
specializes this to the actual standard-coordinate positive suffix using
the proved Gaussian laws, for any separately unit-Lipschitz terminal.
At that verification the outer zero-mass root average and original
auxiliary-pressure identity were separate proof obligations; the preceding
completion record now proves both.

A temporary `lake env lean` audit of all 42 supporting theorems reports only
`propext`, `Classical.choice` and `Quot.sound`, or a subset. The capstone still
reports `sorryAx`. `git diff --check`, local documentation links, new
declaration-owner entries, and new-source whitespace, namespace and proof-hole
checks passed. The Parisi/Common scan still finds only `ParisiLowerBound.lean:44`;
the capstone has no diff. All edits stayed inside Parisi; the temporary audit
file was removed. The root site identity, original pressure transport/deletion
and field averaging have now been proved in the preceding completion record.
Compact uniformization and main-estimate
assembly, concentration, field-fluctuation transfer, localization and lower
interpolation remain open.

## Completed driven covariance, matrix correction and zero-mass root extraction

Verified on 2026-10-13 with Lean 4.34.0-rc2:

```text
lake build SpinGlass.Parisi.Coupled.CoupledCanonicalRootCompression SpinGlass.Parisi.Coupled.CoupledCanonicalSignedGap SpinGlass.Parisi.Coupled.CoupledMainNear SpinGlass.Parisi.Coupled.CoupledMainRootSigned SpinGlass.Parisi.Coupled.CoupledMainInnerUniform SpinGlass.Parisi.Coupled.CoupledMainOuterUniform SpinGlass.Parisi.Coupled.CoupledMainZeroTime SpinGlass.Parisi.Minimizer.Full SpinGlass.Parisi.ParisiLowerBound
```

The combined leaf/consumer build passed with 3676 jobs. Four new owners prove
38 supporting theorems: 11 in CoupledCanonicalEndpoints, 6 in
CoupledCanonicalCovariance, 6 in CoupledCanonicalLevelSum and 15 in
CoupledCanonicalRootCompression. The finite split-block walk and exact driven
projection prove the actual before/after endpoints and arbitrary profile
increments. Clamping at the absolute overlap retains exactly shared driven
increments. Actual driven variances, Gaussian columns and the profile's
evenness give the signed covariance equations. The four matrix entries give
the labelled correction and its raw finite coupled level-sum identity.

The full zero-mass prefix is extracted from the actual stable merge; the
remaining suffix is nonempty and its concrete masses are positive, monotone
and at most one. The additional independent root expectation at p=0 belongs
to that prefix. Every root correction vanishes, and the positive suffix
retains the exact old correction. No zero mass is supplied to a cascade
comparison in these proofs. A root-compressed Gaussian law and physical
pressure comparison still require proof.

A temporary `lake env lean` audit of all 38 supporting theorems reports only
`propext`, `Classical.choice` and `Quot.sound`, or a subset. The unchanged
capstone still reports `sorryAx`. `git diff --check`, local documentation
links, declaration-owner checks, and new-source whitespace, namespace and
proof-hole checks passed. The Parisi/Common scan still finds only
`ParisiLowerBound.lean:44`; the capstone has no diff. All edits stayed inside
Parisi, and the temporary audit file was removed.
The next deliverable is the root-compressed
matrix/covariance API and aggregated product-Gaussian root columns, followed
by paired recursion transport, deterministic deletion and compact uniformization.
Concentration, field-fluctuation transfer, localization and interpolation
remain open.

## Completed canonical strictness and overlap path

Verified on 2026-10-13 with Lean 4.34.0-rc2:

```text
lake build SpinGlass.Parisi.Coupled.CoupledCanonicalSignedGap SpinGlass.Parisi.Coupled.CoupledCanonicalPath SpinGlass.Parisi.Coupled.CoupledMainNear SpinGlass.Parisi.Coupled.CoupledMainRootSigned SpinGlass.Parisi.Coupled.CoupledMainInnerUniform SpinGlass.Parisi.Coupled.CoupledMainOuterUniform SpinGlass.Parisi.Coupled.CoupledMainZeroTime SpinGlass.Parisi.ParisiLowerBound
```

The combined leaf/consumer build passed with 3672 jobs. The root-prefix
proof's function-composition equality was repaired, and its actual paired
list prefix was proved. CoupledCanonicalSignedGap adds the negative one-site
strict comparison and the combined signed outside-neighbor witness theorem.
CoupledCanonicalPath defines the concrete scalar and matrix overlap paths;
it proves exact driven projection, nonnegative increments, terminal value
one, monotonicity, admissibility, one-piece increments, constant auxiliary
coordinates and zero terminal diagonal defect. These conclusions do not
assume a covariance or pressure comparison.

A temporary `lake env lean` audit checked 41 theorems in
CoupledCanonicalWitness, CoupledMixedMassGap, CoupledCanonicalMagnitudeGap,
CoupledCanonicalRootPrefix, CoupledCanonicalSignedGap and CoupledCanonicalPath.
Every supporting theorem uses only `propext`, `Classical.choice` and
`Quot.sound`, or a subset. The unchanged capstone still reports `sorryAx`.
`git diff --check`, local documentation links and new-source whitespace,
namespace and proof-hole checks passed. The Parisi/Common proof-hole scan
still finds only `ParisiLowerBound.lean:44`. Temporary audit files were removed;
all source and documentation edits stayed inside Parisi.
The next lemma is the concrete driven-piece prefix endpoint identity,
followed by covariance columns, coupled correction, Gaussian recursion
transport, auxiliary deletion and compact uniformization. Concentration,
field-fluctuation transfer, localization and lower interpolation remain open.

## Completed canonical labels, scalar regrouping and correction

Verified on 2026-10-13 with:

```text
lake build SpinGlass.Parisi.Coupled.CoupledCanonicalOrder SpinGlass.Parisi.Coupled.CoupledCanonicalCorrection SpinGlass.Parisi.Coupled.CoupledOppositeColeHopf SpinGlass.Parisi.Variational.ParisiColeHopfRearrangement SpinGlass.Parisi.Coupled.CoupledMainZeroTime SpinGlass.Parisi.Coupled.CoupledMainOuterUniform SpinGlass.Parisi.Coupled.CoupledMainInnerUniform SpinGlass.Parisi.Minimizer.Full SpinGlass.Parisi.ParisiLowerBound
```

The combined build passed with 3666 jobs. Five new owners prove 39 public
theorems: 6 in ParisiScalarRegrouping, 8 in CoupledCanonicalPieces,
8 in CoupledCanonicalScalar, 4 in CoupledCanonicalCorrection and
13 in CoupledCanonicalOrder.

The actual labelled auxiliary and driven pieces are sorted by physical mass.
Their effective scalar mass is the old interval mass. The construction uses
an original interval index in Fin(k+2), allowing a root or terminal split;
its driven list has k+3 pieces and its merged list has 2k+5 pieces. Root
splitting adds an independent zero-mass expectation. Both source lists
occur unchanged as sublists of the physical sort, including tied masses.
Every piece occurs in the merged list, providing concrete gap witnesses.

`parisiCanonicalVarianceBlock_sum` proves (14.376) interval by interval
from the actual profile derivatives, admissible overlaps and closed time
interval. The scalar grouping proof allows arbitrary orders of tied
pieces and uses the actual Gaussian semigroup at mass zero as well.
`coleHopfIterateList_parisiCanonical_sorted_eq_full` identifies the sorted
canonical scalar recursion with the old full recursion for every Lipschitz
terminal. `randomFieldColeHopfListValue_parisiCanonical_sorted_eq` identifies
its actual external-field expectation with the old closed Parisi value.
`randomFieldPairColeHopfListValue_parisiCanonical_le` proves the resulting
non-strict canonical one-site comparison under a probability law with finite
first moment. No scalar regrouping identity is supplied as a hypothesis.

`sum_parisiCanonicalMerged_correction_eq` proves that the actual labelled
shared/independent correction sum equals `parisiCorrection`. The two split
increments telescope, and shared half masses cancel the doubled factor.
Identifying this labelled sum with the finite coupled covariance level sum
still requires the merged overlap-path and physical-law construction.

The expanded temporary axiom audit checked 532 supporting declarations in
68 coupled owners and ten variational owners, including
`measurable_cascadeTiltTanhSq`. Every supporting declaration uses only
`propext`, `Classical.choice` and `Quot.sound`, or a subset. The unchanged
capstone still reports `sorryAx`; the proof-hole scan of Parisi and Common
finds only `ParisiLowerBound.lean:44`. The capstone has no diff. All edits
stay inside Parisi. `git diff --check`, local documentation-link and
declaration-owner checks passed, as did whitespace and namespace checks on
all five new sources. Temporary audit files were removed. The next tasks are
canonical physical Gaussian transport,
deletion and coupled correction identification, actual outside-neighbor
strictness, compact uniformization and full main-estimate assembly. Later
concentration, field-fluctuation transfer, localization and interpolation
remain open.

## Completed rearrangement and paired Gaussian equality inputs

Verified on 2026-10-13 with:

```text
lake build SpinGlass.Parisi.Coupled.CoupledOppositeColeHopf SpinGlass.Parisi.Variational.ParisiColeHopfRearrangement SpinGlass.Parisi.Coupled.CoupledMainZeroTime SpinGlass.Parisi.Coupled.CoupledMainOuterUniform SpinGlass.Parisi.Coupled.CoupledMainInnerUniform SpinGlass.Parisi.Minimizer.Full SpinGlass.Parisi.ParisiLowerBound
```

The combined build passed with 3661 jobs. Eight new variational owners prove
51 public theorems: 5 in ParisiExponentialMix, 4 in ParisiNormalizedEntropy,
4 in ParisiColeHopfSwapKernel, 8 in ParisiColeHopfSwapPositive,
7 in ParisiColeHopfSwapZeroKernel, 4 in ParisiColeHopfSwapZero,
4 in ParisiColeHopfSwap and 15 in ParisiColeHopfRearrangement.
Eight new coupled owners prove 63 public theorems: 8 in CoupledSharedColeHopf,
8 in CoupledSignedColeHopf, 16 in CoupledPairColeHopf,
2 in CoupledColeHopfEquality, 13 in CoupledPairRecursion,
4 in CoupledPairEquality, 8 in CoupledPairGap and 4 in CoupledOppositeColeHopf.

`coleHopf_swap_le` and `coleHopf_swap_logCoshIterate_lt` complete Lemma
14.10.5. The zero-mass case uses the actual expectation and normalized
entropy comparison; strictness is not inferred from a limiting non-strict
bound. The positive-mass normalized kernel has proved product integrability,
so Fubini and equality of the actual tilts give the shift identities.
The actual suffix is strictly convex from its positive curvature estimate,
including unordered masses in [0,1] and zero variances.

`coleHopfIterateList_le_insertionSort` proves finite rearrangement.
An inversion at two nonzero variances makes it strict. Equality after a
probability external-field average with finite first moment forces active
mass order. `randomFieldColeHopfListValue_parisiFull_eq` identifies the
original closed Parisi comparator, including root expectation and terminal
mass one. Canonical merged-list scalar regrouping (14.376) is still needed.

`pairColeHopfIterate_logCosh_le_scalar` proves (14.372)-(14.375) for the
actual finite Gaussian operators, with exact independent exponential and
mass-zero integral identities. `signedPairColeHopf_logCoshList_eq_implies_fields_eq`
proves the signed field condition (14.381) for the actual suffix. Equality
propagates through a nonzero independent plane or correlated diagonal, also
at mass zero. The field-averaged sorted-scalar equality forces active mass
order. `pairColeHopfIterate_lt_scalar_of_independent_before_correlated`
gives strictness when a nonzero independent mark precedes a positive
nonzero correlated mark, with arbitrary intervening layers. Opposite
nonzero directions give full paired support and the signed-root strict
gap, allowing both root masses to be zero. Both strict gaps survive the
external-field average under the finite first moment assumption.

A temporary `lake env lean` audit checked all 489 supporting declarations
in sixty-three coupled and nine variational owners, including
`measurable_cascadeTiltTanhSq`. They use only `propext`, `Classical.choice`
and `Quot.sound`, or a subset. The unchanged nondegenerate capstone still
reports `sorryAx`. The proof-hole scan of Parisi and Common finds only the
original `ParisiLowerBound.lean:44`; that file has no diff. No build blocker
remains. `git diff --check`, documentation-link and declaration-owner checks
passed; all sixteen new sources also have no trailing whitespace. Temporary
audit files were removed. All source and document edits stay inside Parisi. The next task is
the actual canonical merged arrays, Gaussian deletion, theta correction,
scalar regrouping and the outside-neighbor application, followed by full
uniform assembly, concentration, field-fluctuation transfer, localization
and lower interpolation.

## Completed uniform far outer and zero-time cases

Verified on 2026-10-13 with:

```text
lake build SpinGlass.Parisi.Coupled.CoupledMainZeroTime SpinGlass.Parisi.Coupled.CoupledMainOuterUniform SpinGlass.Parisi.Coupled.CoupledMainInnerUniform SpinGlass.Parisi.Coupled.CoupledMainNear SpinGlass.Parisi.Coupled.CoupledMainRootSigned SpinGlass.Parisi.Minimizer.Full SpinGlass.Parisi.Variational.ParisiQuantitativeMass SpinGlass.Parisi.ParisiLowerBound
```

The build passed with 3645 jobs. Ten new outer owners prove 41 public theorems:
9 in CoupledOuterFreeMass, 1 in CoupledOuterFreeAuxiliary, 10 in
CoupledOuterFreeSite, 3 in CoupledOuterFreeCorrection, 2 in CoupledOuterFreeBound,
5 in CoupledOuterFreeComparison, 3 in CoupledOuterMassGain, 1 in CoupledMainOuterFar,
5 in CoupledOuterFreeContinuity and 2 in CoupledMainOuterUniform.
CoupledZeroTimeComparison and CoupledMainZeroTime prove two public theorems each.

`exists_uniform_randomFieldParisiAuxPairPressure_outer_far_gap` proves
Proposition 14.8.5 with the tolerance chosen before all site laws and MIN
parameters. Each MIN has one positive pressure gap for all outer levels,
times, separated overlaps, volumes and probability realizations. The actual
free scalar outer mass may exceed one because its shared physical mass is
halved. The terminal matching mass one, k=0, and a collapsed terminal overlap
interval are retained. Auxiliary deletion, scalar identities, actual mass
derivative, exact theta correction, physical pressure normalization, finite
comparison and i.i.d. field average are proved. Convexity and the uniform
upper mass estimate give the negative mass response at zero coupling slope;
continuous scalar witnesses give the compact uniform gap.

`randomFieldParisiAuxPairPressure_zero_le_quadratic_gap` proves Proposition
14.8.7 with coefficient 1/2 at every original level and every realizable
overlap, including negative overlaps. The zero driven covariance comparison
requires no neighboring-interval restriction. The concrete stationary
q-moment identifies the actual coupling derivative, and terminal normalization
gives the original physical pressure. No supplied derivative or final gap is
assumed.

A temporary `lake env lean` audit checked 375 supporting declarations in
fifty-five coupled owners and ParisiProfileStrictGap, including
`measurable_cascadeTiltTanhSq`. They use only `propext`, `Classical.choice`
and `Quot.sound`, or a subset. The unchanged nondegenerate capstone still
reports `sorryAx`. The scan of Parisi and Common finds only the original hole
at `ParisiLowerBound.lean:44`. That file has no diff. Source and document edits
stay inside Parisi. Positive-time outside-neighbor comparison, full
main-estimate assembly, concentration, field-fluctuation transfer,
localization and lower interpolation remain open.

## Completed uniform far inner case

Verified on 2026-10-13 with:

```text
lake build SpinGlass.Parisi.Coupled.CoupledMainInnerUniform SpinGlass.Parisi.Coupled.CoupledMainNear SpinGlass.Parisi.Coupled.CoupledMainRootSigned SpinGlass.Parisi.Minimizer.Full SpinGlass.Parisi.Variational.ParisiQuantitativeMass SpinGlass.Parisi.ParisiLowerBound
```

The build passed with 3633 jobs. Twelve new owners prove 51 public theorems:
10 in CoupledInnerFreeMass, 1 in CoupledInnerFreeAuxiliary, 10 in
CoupledInnerFreeSite, 5 in CoupledInnerFreeCorrection, 2 in CoupledInnerFreeBound,
5 in CoupledInnerFreeComparison, 3 in CoupledInnerMassGain, 2 in CoupledMainInnerFar,
7 in CoupledInnerFreeContinuity, 1 in CoupledCompactWitness, 2 in
CoupledMainInnerUniform and 3 in ParisiProfileStrictGap.

`exists_uniform_randomFieldParisiAuxPairPressure_inner_far_gap` proves the
far part of Proposition 14.8.2 from the original profile, admissibility,
fixed-level MIN and near-infimum assumptions. It chooses the tolerance before
all site laws and MIN parameters. For each MIN, one positive pressure gap
works across inner levels, times, separated overlaps, volumes and Gaussian
probability realizations. The actual free coupled mass range, zero auxiliary
deletion, paired scalar identity, mass derivative, theta correction, physical
pressure comparison and i.i.d. field average are proved. Strict profile
convexity permits zero curvature at zero. Uniform Cole-Hopf moduli prove
continuity of the scalar witnesses at all closed endpoints; a finite cover
gives the uniform pressure gap without overlap continuity of the constrained
pressure. Empty far regions and k=0 are included.

A temporary `lake env lean` audit checked 330 public supporting declarations
in forty-three coupled owners and ParisiProfileStrictGap, including
`measurable_cascadeTiltTanhSq`. Every supporting declaration reports only
`propext`, `Classical.choice` and `Quot.sound`, or a subset. The unchanged
nondegenerate capstone still reports `sorryAx`. The remaining main-estimate
cases are far outer, outside-neighbor and zero time; concentration,
field-fluctuation transfer, localization and lower interpolation remain open.

## Completed whole initial interval including negative overlaps

Verified on 2026-10-12 with the explicit consumer build:

```text
lake build SpinGlass.Parisi.Coupled.CoupledMainRootSigned SpinGlass.Parisi.Coupled.CoupledMainNear SpinGlass.Parisi.Variational.ParisiQuantitativeMass SpinGlass.Parisi.ParisiLowerBound
```

The build passed with 3621 jobs. Seven new owners prove 46 public theorems:
6 in CoupledSignedRootSite, 7 in CoupledSignedRootLaw, 13 in
CoupledRootSignedGain, 2 in CoupledRootSignedTransport, 9 in
CoupledRootSignedVariance, 6 in CoupledRootSignedComparison and 3 in
CoupledMainRootSigned. The actual raw four-column signed recursion has its
concrete averaged product-gradient slope, proved zero-mass limit and canonical
response identification. The finite-volume comparison discharges its signed
covariance and tangent inputs, exact correction and terminal normalization,
and averages the actual i.i.d. external-field law. The complete initial interval
has a uniform physical-pressure penalty with coefficient 1/8, with the
tolerance preceding MIN parameters, volume and time.

A temporary `lake env lean` audit checked all 278 public supporting theorems
in thirty-two coupled owners, together with `measurable_cascadeTiltTanhSq`,
for 279 supporting declarations. They report only `propext`, `Classical.choice`
and `Quot.sound`, or a subset. The unchanged nondegenerate capstone still
reports `sorryAx`. The scan of SpinGlass/Parisi and Common finds only
`ParisiLowerBound.lean:44`. That file has no diff. All source/document edits
stayed inside Parisi. Far/outside-interval and zero-time cases, concentration,
field-fluctuation transfer, localization and lower interpolation remain open.

The earlier sections below record their respective continuation checkpoints.
Their then-open signed tasks are now resolved by this continuation.

## Completed whole nonnegative interval and signed response

Verified on 2026-10-12 with the explicit consumer build:

```text
lake build SpinGlass.Parisi.Coupled.CoupledRootSignedResponse SpinGlass.Parisi.Coupled.CoupledIndependentPair SpinGlass.Parisi.Coupled.CoupledMainNear SpinGlass.Parisi.Variational.ParisiQuantitativeMass SpinGlass.Parisi.ParisiLowerBound
```

The build passed with 3614 jobs. The five new owners prove 35 public theorems:
8 in CoupledRootNonnegative, 10 in CoupledIndependentPair, 7 in
CoupledGaussianCorrelation, 5 in CoupledGaussianPairLaw and 5 in
CoupledRootSignedResponse. `cascadeTilt_shiftedTanh_eq` is now public with its
statement and proof unchanged. The whole nonnegative initial interval has a
uniform physical-pressure penalty with coefficient 1/8. The signed interval
has uniform canonical response separation with factor $(1-t_0)/2$; connecting
that moment to the actual signed coupling slope and pressure remains open.

A temporary `lake env lean` audit checked all 232 public supporting theorems
in twenty-five coupled owners, together with `measurable_cascadeTiltTanhSq`,
for 233 supporting declarations. They report only `propext`, `Classical.choice`
and `Quot.sound`, or a subset. The unchanged nondegenerate capstone still
reports `sorryAx`. The scan of SpinGlass/Parisi and Common finds only
`ParisiLowerBound.lean:44`. That file has no diff. All source/document edits
stayed inside Parisi. Negative-root pressure, far/outside-interval cases,
concentration, field-fluctuation transfer, localization and lower interpolation
remain open.

## Completed nearby root pressure comparison

The initial nonnegative-overlap continuation passed on 2026-10-12:

```text
lake build SpinGlass.Parisi.Coupled.CoupledMainRoot SpinGlass.Parisi.Coupled.CoupledMainNear SpinGlass.Parisi.ParisiLowerBound
```

The explicit build passed with 3609 jobs. Five new root owners prove 40 public
theorems: actual Cole-Hopf value/gradient limits, positive root insertion's
one-site value/slope and gain, covariance/total-variance witnesses, exact
correction and auxiliary deletion, finite-volume and i.i.d. field comparisons,
then the zero-mass pressure gain and uniform nearby root estimate.
The new final declarations are
`randomFieldParisiAuxPairPressure_root_le_gain` and
`exists_uniform_randomFieldParisiAuxPairPressure_root_near_gap` in
[CoupledMainRoot.lean](../Coupled/CoupledMainRoot.lean). The first applies to
all nonnegative overlaps below $q_1$; the uniform quadratic estimate is nearby.
Neither theorem covers negative overlaps or the remaining main-estimate cases.

A temporary `lake env lean` audit checked all 196 public supporting theorems
in twenty coupled owners, together with `measurable_cascadeTiltTanhSq`, for
197 supporting declarations. They report only `propext`, `Classical.choice`
and `Quot.sound`, or a subset. The unchanged nondegenerate capstone still
reports `sorryAx`. The proof-hole scan of SpinGlass/Parisi and Common finds
only `ParisiLowerBound.lean:44`, and that file has no diff. Source and document
edits stayed inside Parisi. No build blocker remains. The full initial
interval, other far/outside-interval cases, concentration, field-fluctuation
transfer, localization and lower interpolation remain open.

## Completed nearby physical pressure comparison

The concrete finite-volume continuation passed on 2026-10-12:

```text
lake build SpinGlass.Parisi.Coupled.CoupledMainNear SpinGlass.Parisi.ParisiLowerBound
```

The explicit build passed with 3604 jobs. It includes the actual profile
variance/covariance witnesses, matching correction, finite-volume split
comparison, field coordinate bound and i.i.d. field average, physical auxiliary
Gaussian-law transport, deterministic-level deletion, original-level arrays,
terminal mass-one normalization and nearby original-pressure comparison.
A temporary `lake env lean` audit of all 156 public supporting theorems in
these fifteen coupled owners, together with the public
`measurable_cascadeTiltTanhSq`, checked 157 declarations. Every supporting
declaration reports only `propext`, `Classical.choice` and `Quot.sound`, or
a subset. The separate original capstone audit still reports `sorryAx`.
The proof-hole scan of SpinGlass/Parisi and Common finds only
`ParisiLowerBound.lean:44`; its file has no diff. No source claims or assumptions
there were changed. All source and documentation edits stayed inside Parisi.
`git diff --check` passed. Root and far main-estimate cases, concentration,
field-fluctuation transfer, localization and lower interpolation remain open.

## Completed variance and curvature inputs

The concrete coupling-moment continuation passed on 2026-10-12:

```text
lake build SpinGlass.Parisi.Coupled.CoupledGaussianMix SpinGlass.Parisi.Coupled.CoupledResponseGain SpinGlass.Parisi.ParisiLowerBound
```

The explicit build passed with 3593 jobs, including CoupledResponseMoment,
CoupledVarianceWitness and the changed Coupled/Derivative/Zero dependency.
An axiom audit of all 49 public theorems in CoupledResponseMoment,
CoupledResponseGain, CoupledVarianceWitness and CoupledGaussianMix, together with the
newly public `measurable_cascadeTiltTanhSq`, reports only `propext`,
`Classical.choice` and `Quot.sound`. The separate nondegenerate capstone audit
still reports `sorryAx`. No source claims in ParisiLowerBound were changed.
The proof-hole scan of SpinGlass/Parisi and Common still finds only its original
hole at line 44. All source edits in this continuation stayed inside Parisi.

[ParisiHeatTwo.lean](../Variational/ParisiHeatTwo.lean) now proves forward and
backward heat calculus using two integrand derivatives, including zero
variance. Its four-jet time derivative includes component two, so no fifth
terminal derivative is needed.
[ParisiMomentDissipation.lean](../Variational/ParisiMomentDissipation.lean)
proves the actual local second-moment dissipation with integrand
$2m(B'')^3-(B''')^2$. The sharp bounds give coefficient 146, which survives
the fixed baseline prefix and the probability field/root average, with both
variance endpoints included. The exact declarations are
`abs_parisiRootUSpatialMoment_two_sub_le` and
`abs_parisiRightUSpatialMoment_two_sub_le`.
[ParisiVarianceTaylor.lean](../Variational/ParisiVarianceTaylor.lean) consumes
these bounds to prove uniform cubic remainders for actual root/nonroot U.
`abs_parisiRootf_sub_variance_quadratic_le_of_isMin` and its nonroot counterpart
use actual q-stationarity and retain the exact profile correction above.
Their coefficient 146 is independent of the levels, parameters and field law.

The completed spatial owners are
[ParisiSpatialBounds.lean](../Variational/ParisiSpatialBounds.lean),
[ParisiSpatialThird.lean](../Variational/ParisiSpatialThird.lean), and
[ParisiFirstOverlap.lean](../Variational/ParisiFirstOverlap.lean).
They give the invariant $0\le A''\le1-(A')^2$, layer value increments bounded
by half the variance, telescoping variances, lower curvature
$e^{-2V}/\cosh^2 x$, and first overlap
$q_1\ge e^{-4V}\mathbb E\tanh^2 h>0$, where
$V=\xi'(1)-\xi'(0)$. Ordered masses telescope in the first two derivatives of
the actual cascade log density, yielding bounds by two. Differentiating the
transported terminal gradient gives the uniform third derivative bound twelve,
also for the split layer and zero inserted mass. This is a sufficient bridge
for the Taylor use of (14.272); its sharper coefficient four is not asserted.

[ParisiMomentBounds.lean](../Variational/ParisiMomentBounds.lean) bounds the actual
first two U moments in [0,1] after all prefix and field averages, gives uniform
Lipschitz control of the first moment, and bounds U' and U'' by [0,1] and [-1,0].
[ParisiOverlapCurvature.lean](../Variational/ParisiOverlapCurvature.lean) proves
the root/nonroot endpoint second derivatives from stationarity and the actual
second spatial moments, and uniform curvature tolerances for both intervals.
It does not assert the rate-specific sixth-root bound.
Check the profile remainder against `TalagrandXiCondition`: its third derivative
is not stated to be continuous or bounded. Do not infer such a uniform bound
solely from the existence and nonnegativity of that derivative.

The quantitative inner-mass estimate (14.264) is now proved in
[ParisiQuantitativeMass.lean](../Variational/ParisiQuantitativeMass.lean):
`exists_uniform_parisiRootf_lower_bound` and
`exists_uniform_parisiRightf_lower_bound` give $f\ge-4\sqrt{M\varepsilon}$.
Each f is twice the actual inserted-mass derivative. M depends only on ξ and
is selected before k, parameters, field law and tolerance. Root upper mass B
may be arbitrarily small and includes k=0, B=1. The nonroot upper endpoint
includes mass 1 and compares the old closed functional at `qUpdate qs p.succ u`.
Global infimum comparison supplies near-minimality across the split dimensions;
fixed-level minimality is used only for those endpoint comparisons.

[ParisiMassPropagation.lean](../Variational/ParisiMassPropagation.lean) proves
the full ordered-prefix Taylor estimate. The logarithmic cascade-density
perturbation telescopes to twice the input perturbation, independent of prefix
length. This controls changes of the transported mass derivative together with
the centered single-layer second-mass bound. Field/root averaging requires only
an integrable spatial shift. The earlier conditional-variance route was not
needed. The mirror free outer mass now has a uniform Taylor bound, lower
endpoint comparison and actual U/f bridge, including the terminal old interval
of mass 1. Its square-root upper estimate has the same allowed dependencies.
Its initial spatial moments, q-stationarity, nonterminal f right endpoint,
second-moment variance bound, cubic U/f remainder and endpoint curvature now
compile. The mirror profile conversion and uniform critical response gap now
also compile; the time-dependent coupling-to-response bridge and later coupled
applications remain.

The proved U/f bridge is
[ParisiSplitResponse.lean](../Variational/ParisiSplitResponse.lean): root uses the
full post-root iterate; nonroot inner mass uses `splitParisiMassRight`, prefix
length p.val and suffix `parisiQSuffix ... p.castSucc`. Both U'(0) identities
are derived from the actual old q-moments, with the field/root product law and
Fubini proved. The nonroot f left endpoint is
`parisiRightf_left_endpoint_eq_zero_of_isMinOn`; its mass stationarity is in
[ParisiMassRecursion.lean](../Variational/ParisiMassRecursion.lean).

The profile conversion uses `TalagrandXiCondition` and its consequences in
[Parameters.lean](../Minimizer/QVariation/Parameters.lean), the stationary f
estimates in [ParisiVarianceTaylor.lean](../Variational/ParisiVarianceTaylor.lean),
and book pp. 410-414. The concrete conversion and uniform curvature tolerance
are in ParisiProfileRemainder.lean and ParisiOverlapCurvature.lean.
First-overlap separation is uniform in the chosen MIN.
The C4 suffix bound serves regularity only and may depend on its levels; the
compiled moment and cubic variance coefficients have no such dependence.

Completed declarations and checks on 2026-10-11:

| Owner | Verified additions |
| --- | --- |
| [Minimizer/Full.lean](../Minimizer/Full.lean) | `randomFieldParisiInf_le_closedRandomFieldParisiFunctional`, `randomFieldParisiFunctional_sub_lt_closed_of_near_inf` |
| [ParisiMVariation.lean](../Variational/ParisiMVariation.lean) | `splitParisiMassRight_mem_domain`, `splitParisiRight_mem_parameterDomain`, `randomFieldParisiInf_le_split_left`, `randomFieldParisiInf_le_split_right`, `randomFieldParisiFunctional_sub_lt_split_left_of_near_inf`, `randomFieldParisiFunctional_sub_lt_split_right_of_near_inf` |
| [ParisiMassDerivative.lean](../Variational/ParisiMassDerivative.lean) | `hasDerivAt_coleHopf_exponent_zero`, `hasDerivAt_coleHopf_mass`, `exists_uniform_coleHopf_mass_second_derivative_bound`, `hasDerivAt_coleHopfIterate_mass_layer`, `exists_uniform_coleHopfIterate_mass_derivative_bound`, `hasDerivWithinAt_integral_integral_coleHopfIterate_mass_layer`, `exists_uniform_parisiQSuffix_mass_second_derivative_bound` |
| [ParisiMassRecursion.lean](../Variational/ParisiMassRecursion.lean) | `closedParisiX₀_mass_update_eq`, `randomFieldParisiMassMoment`, `hasDerivWithinAt_randomFieldParisiX₀_mass_update`, `parisiMassPenalty_mass_update_eq`, `hasDerivWithinAt_closedRandomFieldParisiFunctional_mass_update` |
| [ParisiMassRecursion.lean](../Variational/ParisiMassRecursion.lean) | `ParisiMAdmissible.eventually_mass_update`, `isLocalMin_closedRandomFieldParisiFunctional_mass_update_of_isMinOn`, `randomFieldParisiMassMoment_sub_theta_eq_zero_of_isMinOn` |
| [ParisiMVariation.lean](../Variational/ParisiMVariation.lean) | `splitParisiLeftMassDeriv`, `splitParisiRightMassDeriv`, `hasDerivWithinAt_closedRandomFieldParisiFunctional_split_left_mass`, `hasDerivWithinAt_closedRandomFieldParisiFunctional_split_right_mass`, `splitParisiLeftMassDeriv_left_endpoint`, `splitParisiRightMassDeriv_right_endpoint` |
| [ParisiRootMVariation.lean](../Variational/ParisiRootMVariation.lean) | Root constructors, closed-domain membership, zero-mass/empty-interval identities, global comparison, root mass derivative |
| [ParisiRootMVariation.lean](../Variational/ParisiRootMVariation.lean) | `closedRandomFieldParisiFunctional_split_root_upper_mass`, `closedRandomFieldParisiFunctional_split_root_zero_le_upper_of_isMin` |
| [ParisiMassPropagation.lean](../Variational/ParisiMassPropagation.lean) | Actual cascade density logarithm, uniform perturbation bound, `exists_uniform_coleHopfIterateMassDeriv_lipschitz_bound`, `exists_uniform_integral_coleHopfIterate_mass_taylor_bound` |
| [ParisiQuantitativeMass.lean](../Variational/ParisiQuantitativeMass.lean) | Actual mass-coordinate Taylor estimate, root/nonroot upper endpoint comparisons and `exists_uniform_parisiRootf_lower_bound`, `exists_uniform_parisiRightf_lower_bound` |
| [ParisiSpatialRegularity.lean](../Variational/ParisiSpatialRegularity.lean) | `parisiQSuffix_spatial_regular_four`, `iteratedDeriv_coleHopf_one_two_bounds` |
| [ParisiVarianceResponse.lean](../Variational/ParisiVarianceResponse.lean) | Concrete response/moment definitions, zero-mass response, matching-mass baseline, `hasDerivAt_coleHopfIterate_split_mass_of_pos` |
| [ParisiVarianceAveraging.lean](../Variational/ParisiVarianceAveraging.lean) | Actual suffix variance derivatives and concavity under any fixed probability law; uniform-in-variance spatial moment bounds |
| [ParisiVariancePropagation.lean](../Variational/ParisiVariancePropagation.lean) | Actual suffix derivatives, dissipation and concavity after fixed-prefix and probability-law averages; prefix/field-independent response envelope |
| [ParisiSplitResponse.lean](../Variational/ParisiSplitResponse.lean) | Actual root/nonroot inner-mass recursion identities, U/f normalization, variance derivatives, concavity, U'(0)=q_r, f(q_r)=f'(q_r)=0, and nonroot f(q_{r-1})=0 from fixed-level mass minimality |
| [MeasurableParamDeriv.lean](../../../Common/Mathlib/Analysis/Calculus/MeasurableParamDeriv.lean) | Within derivative measurability from admissible difference quotients, including both endpoints |

This command passed with 3542 jobs:

```text
lake build Common.Mathlib.Analysis.Calculus.MeasurableParamDeriv SpinGlass.Parisi.Minimizer.QVariation.RandomField SpinGlass.Parisi.Minimizer.Full SpinGlass.Parisi.Variational.ParisiRootMVariation SpinGlass.Parisi.Variational.ParisiVariancePropagation SpinGlass.Parisi.Variational.ParisiQuantitativeMass SpinGlass.Parisi.ParisiLowerBound
```

`git diff --check` passed. A proof-hole scan of SpinGlass/Parisi and Common
found only `ParisiLowerBound.lean:44`. A temporary `lake env lean` audit of
213 public theorems in the thirteen changed proof owners passed: all have only
`propext`, `Classical.choice`, and `Quot.sound`. The separate capstone audit
still reports `sorryAx`. No build blocker remains. The mathematical obligations
are the time-dependent coupling-to-response moment bridge, remaining terminal
endpoint applications, full main estimate,
random-field concentration transfer, localization, and interpolation comparison.

The spatial/moment continuation also passed this explicit leaf and consumer
build with 3547 jobs:

```text
lake build SpinGlass.Parisi.Variational.ParisiSpatialBounds SpinGlass.Parisi.Variational.ParisiSpatialThird SpinGlass.Parisi.Variational.ParisiFirstOverlap SpinGlass.Parisi.Variational.ParisiMomentBounds SpinGlass.Parisi.Variational.ParisiOverlapCurvature SpinGlass.Parisi.Variational.ParisiQuantitativeMass SpinGlass.Parisi.Minimizer.Full SpinGlass.Parisi.ParisiLowerBound
```

A temporary `lake env lean` audit of all 56 public theorems in the five
spatial, first-overlap, moment and endpoint-curvature owners passed with only
`propext`, `Classical.choice`, and `Quot.sound`. The same audit still finds
`sorryAx` in the nondegenerate capstone. The scan of SpinGlass/Parisi and
Common still finds only its original hole at `ParisiLowerBound.lean:44`.
`git diff --check` passed. No capstone completion is claimed by these builds.

The two-derivative heat, second-moment dissipation and cubic variance continuation
passed this explicit leaf and consumer build with 3550 jobs:

```text
lake build SpinGlass.Parisi.Variational.ParisiHeatTwo SpinGlass.Parisi.Variational.ParisiMomentDissipation SpinGlass.Parisi.Variational.ParisiVarianceTaylor SpinGlass.Parisi.Variational.ParisiOverlapCurvature SpinGlass.Parisi.Variational.ParisiQuantitativeMass SpinGlass.Parisi.Minimizer.Full SpinGlass.Parisi.ParisiLowerBound
```

A temporary `lake env lean` audit of all 24 public theorems in the three new
owners and the two endpoint derivative identities passed with only `propext`,
`Classical.choice`, and `Quot.sound`. The capstone still reports `sorryAx`.
The new leaves have no linter warnings. The hole scan of SpinGlass/Parisi and
Common still finds only `ParisiLowerBound.lean:44`; its statements are unchanged.
`git diff --check`, new-source whitespace checks and all local documentation
links passed. The remaining mathematical task is the profile-coordinate
remainder described above; no build blocker remains.

## Source lookup

The source PDF is [Notes/Talagrand-spin-glass-II.pdf](../../../Notes/Talagrand-spin-glass-II.pdf).
Use the existing [text extract](talagrand-reference.txt) for search, not as the
authority for formulas. Do not read the whole extract into context.

The following page ranges use printed book pages; viewer page numbers are
one-based. In this PDF the viewer page is the printed page plus 5 in Chapter 14.

| Material | Printed pages | PDF viewer pages | Read for |
| --- | --- | --- | --- |
| Section 14.4 | 362-371 | 367-376 | Interpolation definitions, endpoints, upper bound |
| Section 14.5 | 371-381 | 376-386 | MIN, target estimates, concentration, proof assembly |
| Section 14.6 | 381-395 | 386-400 | Coupled bounds and Taylor calculus |
| Section 14.7 | 395-414 | 400-419 | Operators, stationarity, mass variations |
| Section 14.8 | 415-419 | 420-424 | Seven cases and compactness assembly |
| Section 14.9 | 419-428 | 424-433 | Critical case proofs |
| Section 14.10 | 428-439 | 433-444 | Outside-interval and zero-time cases |

Useful anchors: (14.101) and Theorem 14.5.1 on p. 373; MIN and Theorem 14.5.4
on pp. 373-374; (14.109) on p. 375; Theorem 14.5.7 on p. 376;
Proposition 14.5.8 on pp. 377-381; random-field caveat after (14.123) on p. 381;
(14.239) on p. 404; (14.283) on p. 414.

For field conditions, read (14.65) on p. 363 together with the nonzero-field
definition on p. 373 and the random-field qualification on p. 381. The Gaussian
Hamiltonian assumption does not make the external field Gaussian. The current
Lean contract explicitly assumes finite second moment; do not infer stronger
field assumptions from a concentration lemma's inputs.

From the repository root:

```text
rg -n '14\.239|14\.250|14\.283' SpinGlass/Parisi/Docs/talagrand-reference.txt
pdftotext -f 378 -l 386 -layout Notes/Talagrand-spin-glass-II.pdf -
```

Inspect the relevant PDF page when extracted subscripts, derivatives, or signs
are ambiguous. Equation numbers are more stable references than extract lines.

## Execution rules

Build the current leaf before a proof edit to distinguish existing failures
from new ones. Finish one consumer-ready result at a time; do not create a chain
of placeholder modules. Read the next consumer's signature before fixing the
helper's quantifiers. Proposed files below should be created only when they have
actual definitions and proofs. Adapt names to the repository structure.

The main estimate and concentration are independent inputs to localization.
The sequence below is a practical single-agent order, not a requirement that
concentration import the main estimate.

## Mass calculus: Section 14.7

Continue from the split comparison above and the existing q-stationarity.
Represent Talagrand's $\Phi$, $U$, and $f$ through the concrete recursion; document
their correspondence to (14.238)-(14.239). Define the inserted-mass derivative
with its actual domain, including one-sided endpoints.

Required outputs:

- The concrete mass derivative identity (14.239), with integrability and
  differentiation under the field expectation proved.
- The formulas and sign control for $U'$ and $U''$, including $U'(0)=q_r$ from
  existing stationarity. State concavity on precisely the book's domain.
- $f(q_r)=f'(q_r)=0$ and the appropriate left-endpoint identity for $r\ge2$.
  Use fixed-level mass minimality for that endpoint identity.
- The needed bounds for mass Taylor remainders and the third overlap derivative.
  Check the current profile assumptions before claiming a global smoothness bound.
- The quantitative $f(u)\ge-M\sqrt{\varepsilon}$ consequence of split
  near-minimality, with constants uniform over the parameters required by the
  book. A bound on the first derivative alone does not control a Taylor remainder.
- Lemma 14.7.15's $q_1\ge1/M$ under nondegeneracy, uniform in the eligible MIN
  approximation; endpoint strictness alone is insufficient.
- Curvature smallness for (14.283). The compiled modulus-based theorem selects
  MIN tolerance for any requested curvature error without claiming the
  sixth-root rate. Retain the book's two interval-length cases; use the
  near-minimality bound or the endpoint identity accordingly.

Exit condition: the case proofs can import these estimates without reopening
the recursion. Check both split orientations and terminal intervals. Bounds
used to select the MIN tolerance must not depend on the MIN chosen afterwards.

## Coupled adapters: Section 14.6

Reuse CoupledProp, CoupledLambdaZero, Coupled/Derivative/First and Zero, and
CoupledSecondDeriv via the exact owners in INDEX.md. Existing averaged zero
coupling and derivative lemmas should be applied before new adapters are added.

Expose the constrained two-copy pressure in the normalization of (14.100).
For realized fields, use `sharedReplicaSiteField` and prove the integrability
needed to average over externalFieldVecLaw. Track the sign parameter for
negative overlaps. Separate witness construction from coupled-bound algebra
and scalar analysis.

Exit condition: a case proof can choose admissible parameters, invoke the
coupled bound, rewrite its zero-coupling value, apply `pairSiteY₀_le_taylor`,
and finish a scalar inequality. It should not manipulate cascade internals.

## Main estimate: Theorem 14.5.7

Suggested new owner: SpinGlass/Parisi/ParisiMainEstimate.lean (not yet present).

First fix the profile, nondegenerate law, and $0\le t_0<1$. Choose a positive
MIN tolerance depending only on those data. For every MIN satisfying that
tolerance, obtain $K>0$ such that, for all relevant volumes, levels, realizable
overlaps, and $0\le t\le t_0$,
$\Psi_r(t,u)\le2\psi(t)-(u-q_r)^2/K$.

Do not omit the smallness choice for the MIN tolerance. The near cases can
use `exists_uniform_parisi_critical_response_gap`, which selects a tolerance
from the profile modulus and the requested time cutoff without asserting the
book's sixth-root rate. CoupledMainNear now proves the actual nearby
nonroot and outer pressure comparisons, including terminal normalization.
The nonnegative root coupled-moment bridge and its finite-volume limit now
compile in CoupledMainRoot. CoupledRootNonnegative proves the whole
nonnegative interval, and CoupledMainRootSigned completes the whole initial
interval including the actual signed physical-pressure application.
The far inner and outer cases now compile in CoupledMainInnerUniform and
CoupledMainOuterUniform, using the proved uniform positive profile tangent
gap with tolerances preceding all MINs. CoupledMainZeroTime proves the
zero-time penalty at every realizable overlap. Positive-time outside-neighbor
comparison and full uniform assembly remain open.

| Book proposition | Range and task |
| --- | --- |
| 14.8.1 | Near left, $q_{r-1}\le u\le q_r$; Taylor in coupling and curvature give quadratic gain |
| 14.8.2 | Far left with $r\ge2$; split variation and convexity give strict gain |
| 14.8.3 | First level with $|u|\le q_1$; preserve the negative-overlap argument |
| 14.8.4 | Near right, $q_r\le u\le q_{r+1}$; mirror critical calculation |
| 14.8.5 | Far right; mirror strict-gain argument |
| 14.8.6 | Positive time outside neighboring overlap interval |
| 14.8.7 | Zero time and $u\ne q_r$ |

For the far region, prove a uniform positive gap on a compact set. A direct
witness approach can replace the abstract infimum $\Psi^*$, but must still
supply the local continuity/upper semicontinuity or finite-cover argument
needed for uniformity. Handle empty far regions separately. Convert a gap
$\delta>0$ into a quadratic penalty using $(u-q_r)^2\le4$, then take finite
maxima over levels/cases.

Exit condition: one theorem matching (14.112), with all choices and constants
in the correct order and an independent leaf build.

## Concentration: Proposition 14.5.8

Active owners: the modules in SpinGlass/Parisi/Concentration, listed above.

Build the constrained/unconstrained recursion, multiplicative weights, and
bounded terminal factor of (14.116)-(14.120). Derive the negative mean of the
logarithmic weighted product from a positive pressure gap, as in (14.121).

The actual pair tilted logarithm now has joint Gaussian and bounded-field
concentration, with variance proxy $N(32(D+v_0d)+16R^2)$. PairTiltRootVariance
accounts for arbitrary root variance and singular interaction covariance.
ProductSubGaussian proves the conditional-mean fluctuation bound and all
joint integrability. PairTiltCombinedConcentration applies it to the actual
observable, and PairTiltBoundedField transfers the result to the original
bounded site law. This completes the bounded-field fluctuation issue left
implicit in the book after (14.123).

PairTiltPressureGap derives the averaged negative mean and an explicit
exponential expectation bound from the actual pair-cascade pressure gap.
ParisiTiltParameters, ParisiPressureIdentification and PairBranchMeeting now
discharge the original coefficient bounds, normalized pressure identification
and exact tree-meeting identity. ParisiBranchConcentration supplies the actual
bounded-field joint-mass bound $2\exp(-cN)$, uniformly over time, level,
overlap and volume. Empty constraints have exactly zero mass.

FieldLawContinuity and FieldTruncation prove arbitrary-law coupling continuity,
nondegeneracy of positive clips and the uniform truncation reduction. Complete
the bounded-law localization and lower bound before invoking that reduction.
If a weaker decay bound replaces (14.114), label it accurately and prove it
suffices after summing over at most $2N+1$ overlap values. Mere convergence to
zero for each overlap is insufficient.

Exit condition: an averaged constrained-mass estimate actually applicable to
the final field law, or a complete approximation bridge with a rate sufficient
for localization. The gap-dependent constant must be independent of volume,
time, and overlap. Do not mark this phase done after only a conditional theorem.

## Localization: Proposition 14.5.6

Suggested new owner: SpinGlass/Parisi/ParisiLocalization.lean (not yet present).

Combine the main estimate with the pressure-gap estimate on the event
$(R_{1,2}-q_r)^2\ge K(\psi(t)-\varphi_N(t)+\varepsilon_1)$.
Sum over realizable overlaps, using the safe bound of $2N+1$ values and handling
empty constraints explicitly.

Choose localization $K$ before $\varepsilon_1$. The volume threshold may depend
on $\varepsilon_1$, but must be uniform over $t\in[0,t_0]$ and the finitely many
levels. The main estimate's $K$ and concentration's gap-dependent constant are
different roles; do not let the latter change the former's quantifier order.

Exit condition: the expectation of the bad-overlap event intersected with the
branch-meeting event is eventually at most $\varepsilon_1$, as in (14.110).
The book uses this joint mass, not a normalized conditional probability requiring
division by the branch-meeting probability.

## Interpolation: Theorem 14.5.4

Suggested new owner: SpinGlass/Parisi/ParisiInterpolationLower.lean (not yet present).

Identify the concrete interpolation and its Parisi-side comparison. Obtain the
exact Guerra derivative remainder, with the repository's normalization; an
already integrated upper bound alone cannot give the lower comparison.
Bound the profile remainder by a constant times $(R_{1,2}-q_r)^2$, proving the
needed regularity from TalagrandXiCondition.

Insert localization and sum over levels to get, eventually and uniformly in
time, $(\psi-\varphi_N)'\le K(\psi-\varphi_N+\varepsilon_1)$, with zero initial
difference and $K$ independent of $\varepsilon_1$. Apply the differential
inequality argument (Lemma A.11.1 in the book), then let $\varepsilon_1$ tend
to zero in an eventual accuracy statement.

Exit condition: (14.107) for eligible MIN at each fixed cutoff below 1, in a
form directly usable by the endpoint proof.

## Endpoint and capstone: Theorems 14.5.2 and 14.5.1

Prove the coarse volume-uniform derivative comparison (14.109). Use endpoint
continuity if derivatives are available only at interior times. Combine the
comparison with interpolation convergence to get an eventual inequality of
the form $\varphi_N(1)\ge\psi(1)-M(1-t_0)-\delta$.

For a requested lower-bound accuracy, choose $t_0$ near 1 first, then a tolerance
allowed by the main/interpolation theorem, then MIN, and finally large volume.
Use $\varphi_N(1)=p_N$, $\psi(1)=P_k$, and $\mathcal P\le P_k$.
The MIN tolerance enables the variational estimates; its near-infimum upper
inequality is not the lower inequality needed in the last comparison.

Replace the capstone hole with a short assembly proof. Preserve the existing
zero-second-moment reduction, convergence squeeze, liminf result, and all their
hypotheses.

Exit condition: all existing claims compile from completed dependencies with
no new project axioms or proof holes.

## Final integration and handoff

Add the completed capstone to the import chain through SpinGlass/Parisi.lean
(or directly through SpinGlass.lean). Build every new leaf when introduced,
then the capstone and full project. Follow [AGENTS.md](../AGENTS.md#validation)
for proof-hole and axiom checks. Update the status table and this plan.

At the end of each proof session, replace the next-task description with a short
record containing: completed declaration and owner; exact commands/results;
remaining mathematical or build blocker; next consumer-ready lemma. Do not
duplicate a full historical log in every document.
