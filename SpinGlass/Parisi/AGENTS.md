# Parisi proof-agent instructions

## Rule

Use mathlib in /Lean/.lake

## Objective and first action

Complete the existing claims in [ParisiLowerBound.lean](ParisiLowerBound.lean),
following Talagrand, Vol. II, Chapter 14, Sections 14.5-14.10. Preserve all public
statements. The open theorem is
`eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy_of_nondegenerate`.
The later reduction and convergence results depend on this hole.

For a new proof session, read [the next task](Docs/EDITING_PLAN.md#next-task)
and the target theorem, then use [INDEX.md](INDEX.md) to find declaration owners.
Read only the source ranges and book pages needed for that task. Do not load the
whole reference extract or all recursion files into context.

The root and nonroot inner-mass U/f identities, q-stationarity, endpoint
comparisons, uniform propagated Taylor remainders and square-root MIN estimates
were compiled on 2026-10-11. The mass constants are independent of the level
count and field law. The next task is the sharp spatial recursion bounds and
uniform first-overlap separation, followed by overlap curvature and the mirror
outer-mass bridge.
See the plan for exact declarations and remaining uniformity requirements.
Recheck the source before implementing anything described as missing.

## Document responsibilities

| Document | Read it for |
| --- | --- |
| [README.md](README.md) | Scope, field semantics, entry points |
| [INDEX.md](INDEX.md) | Exact declaration owners and source lookup |
| [Docs/ARCHITECTURE.md](Docs/ARCHITECTURE.md) | Current evidence, dependencies, mathematical contracts |
| [Docs/EDITING_PLAN.md](Docs/EDITING_PLAN.md) | Next deliverable, phase exit conditions, book page map |

These instructions govern editing. Lean statements govern the formal target;
the book governs the intended argument. If they differ, record the specific
mismatch and prove a bridge; do not silently change either contract.
Documentation is a navigation aid, not evidence of a completed proof.

Paths are relative to this directory unless stated otherwise. Older root
instructions mention pre-reorganization filenames. Apply their mathematical
requirements to the current owners in INDEX.md. In particular, the old
q-derivative completion criteria apply to the Minimizer/QVariation directory.

## Mathematical contracts

- Keep the lower-bound target under a probability law with finite second moment;
  its nondegenerate branch additionally assumes positive second moment. Do not
  replace this by bounded, Gaussian, exponentially integrable, or almost surely
  nonzero fields.
- Check field assumptions against (14.65), the paragraph before Theorem 14.5.2,
  and the qualification after (14.123). Distinguish the book's stated assumptions
  from integrability made explicit in Lean; see the field-source table in README.
- Use `externalFieldVecLaw` for i.i.d. site fields and `sharedReplicaSiteField` for
  replicas of one quenched system. Averaging one constant field across all sites
  gives a different model.
- Preserve `TalagrandXiCondition` and the separate covariance PSD hypothesis.
  Convexity does not establish existence of the Gaussian Hamiltonian. Derive
  needed regularity from the current structure; do not assume global extra
  smoothness or strict positivity of the second derivative at zero.
- Preserve the existing additional Guerra assumptions in the convergence and
  liminf corollaries. They are not assumptions of the eventual lower bound.
- Keep the zero-second-moment reduction downstream of the nondegenerate theorem.
  Do not assume a thermodynamic limit, uniqueness, or Chapter 15 structure theory.
- Fixed-level MIN minimality compares competitors at that level count. A split
  raises the level count: use the global infimum and MIN tolerance for this
  comparison. Do not apply fixed-level `IsMinOn` across different dimensions.
- Select the MIN tolerance after fixing the time cutoff and before selecting
  parameters. State each constant's allowed dependencies. Volume, time, and
  overlap cannot enter the main-estimate constant; localization additionally
  requires independence from its auxiliary tolerance.
- Conditional Gaussian concentration is only part of the random-field argument.
  An averaged pressure gap is not a gap for each realized field. Discharge the
  missing field-fluctuation argument described in the plan.

## Work efficiently

- Inspect the working tree first; preserve ongoing edits and the current module
  organization. Do not restore old paths or perform unrelated refactors.
- Search exact names in INDEX.md before broad searches. Import the owning module,
  not the convenience umbrella, into proof leaves; avoid import cycles.
- State the next consumer's conclusion and quantifiers before proving a helper.
  Finish a usable lemma before starting another dependency layer.
- Reuse Cole-Hopf, cascade, finite Gibbs, and coupled-copy APIs. Search
  SpinGlass/FiniteGibbs and Common/Mathlib/Probability/PointProcess from the
  repository root when the local index has no match.
- Retain conditional reductions as such. Assuming the desired derivative,
  moment bound, or concentration conclusion does not complete a book-level proof.
- Use `Fin`, `qExt`, and `mExt`; preserve fixed endpoints. Compile after changing
  indexing. Treat zero variances by admissible one-sided variations or proved
  nearby-sign arguments.
- Keep namespace `SpinGlass`, explicit binders, and repository Lean options.
  Put book theorem/equation references in bridge-lemma docstrings.
- Do not add `sorry`, `admit`, project axioms, or unsafe proof shortcuts. Audit the
  transitive dependency cone, including helpers outside this directory.
- On handoff, record the exact declaration completed, checks actually run, any
  blocker, and the next smallest lemma in the plan. Source inspection is not a
  successful build.

## Validation

Run commands from the repository root. For proof changes, build the changed leaf
and its relevant consumers. Existing useful targets are:

```text
lake build SpinGlass.Parisi.Minimizer.QVariation.RandomField
lake build SpinGlass.Parisi.Minimizer.Full
lake build SpinGlass.Parisi.Variational.ParisiMassDerivative
lake build SpinGlass.Parisi.Variational.ParisiMassRecursion
lake build SpinGlass.Parisi.Variational.ParisiMVariation
lake build SpinGlass.Parisi.Variational.ParisiRootMVariation
lake build SpinGlass.Parisi.Variational.ParisiVariancePropagation
lake build SpinGlass.Parisi.Variational.ParisiSplitResponse
lake build SpinGlass.Parisi.Variational.ParisiMassPropagation
lake build SpinGlass.Parisi.Variational.ParisiQuantitativeMass
lake build SpinGlass.Parisi.ParisiLowerBound
git diff --check
rg -n '\b(sorry|admit|axiom)\b' SpinGlass/Parisi --glob '*.lean'
```

Inspect scan hits; comments and declarations differ. Compilation may succeed
with a proof hole, so neither check replaces the other. For the final proof
audit, use #print axioms on the capstone in a temporary Lean file and check for
`sorryAx` or new project axioms; ordinary Lean foundations are expected.

SpinGlass.lean imports the convenience module SpinGlass/Parisi.lean, which
currently omits the capstone. After completion, add the capstone to that import
chain and run lake build as well as the explicit leaf build.

For documentation-only changes, verify links, module/declaration names, status
claims, and git diff --check; a full Lean rebuild is unnecessary. Toolchain and
build paths come from lean-toolchain and lakefile.toml. If Git reports ownership
trouble, use a command-local safe.directory setting for this checkout rather
than changing global configuration.

Completion means the original lower-bound claims and their dependency cone have
no proof holes, their assumptions are unchanged, the leaf and umbrella builds
succeed, and the architecture/status documents report that verified state.
