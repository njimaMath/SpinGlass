# Parisi proof-agent instructions

## Objective and first action

Use the existing mathlib installation in the parent Lean workspace's `.lake`.
The four public claims in [ParisiLowerBound.lean](ParisiLowerBound.lean) are
complete. Preserve all statements and assumptions, including
`eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy_of_nondegenerate`.
Do not add proof holes, project axioms, unsafe declarations or stronger hypotheses.

For a new session, read [the next task](Docs/EDITING_PLAN.md#next-task), inspect
the working tree, and use [INDEX.md](INDEX.md) to locate declaration owners.
Read only the source ranges and book pages needed for that task. Recheck the
source before implementing anything described as missing in historical notes.

## Document responsibilities

| Document | Read it for |
| --- | --- |
| [README.md](README.md) | Scope, field semantics and module entry points |
| [INDEX.md](INDEX.md) | Exact declaration owners |
| [Docs/ARCHITECTURE.md](Docs/ARCHITECTURE.md) | Dependencies and mathematical contracts |
| [Docs/EDITING_PLAN.md](Docs/EDITING_PLAN.md) | Next deliverable and validation history |
| [Docs/ANALYTIC.md](Docs/ANALYTIC.md) | Generic analytic topic owners and reuse guidance |

Lean statements govern the formal target; the book governs the intended argument.
If they differ, record the mismatch and prove a bridge without changing either
contract. Documentation is navigation, not evidence of a completed proof.

Paths are relative to this directory. Historical notes may use filenames
from before reorganization: apply their mathematical requirements to the owners
in INDEX.md. The q-derivative completion criteria apply to Minimizer/QVariation.
[Analytic.lean](Analytic.lean) imports the generic Analytic topic modules. The
historical `ARISTOTLE.lean` import is replaced by `SpinGlass.Parisi.Analytic`;
declaration names remain in `SpinGlass.Aristotle`. Group analytic work by
mathematical topic, with basic definitions before derivative and bound modules.
The shared `ProbabilityTheory.coleHopf_translate` and `coleHopfQ_translate`
are owned by [Common ColeHopf](../../Common/Mathlib/Probability/Distributions/Gaussian/ColeHopf.lean);
`coleHopfIterate_translate` and `coleHopfIterate_append` are owned by
[Common CascadeColeHopf](../../Common/Mathlib/Probability/PointProcess/CascadeColeHopf.lean). These replace
former `SpinGlass` declarations; use the shared names through their owner imports.
Keep full-domain derivative measurability as a specialization of
`measurable_derivWithin_param` in
[MeasurableParamDeriv](../../Common/Mathlib/Analysis/Calculus/MeasurableParamDeriv.lean).
Import the declaration owner into proof leaves. Field law
assumptions belong in Field/FieldMoments.lean, independently of stationarity.

## Mathematical contracts

- For every source-attributed theorem, verify that source assumptions imply
  the Lean hypotheses and that the Lean conclusion implies the source result.
  Check definitions, domains, endpoints, quantifier order and constant
  dependencies, not just the displayed formula. Prove any additional analytic
  side conditions from the source assumptions. Label a partial or conditional
  result accurately until those bridges are complete.
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
- Preserve the mathematical scope of `TalagrandXiCondition` and the separate
  covariance PSD hypothesis. Any replacement interface needs proved bridges
  that preserve the existing capstone contracts.
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

## Minimal API and proof obligations

Follow mathlib's [review guidance](https://leanprover-community.github.io/contribute/pr-review.html)
and [values](https://leanprover-community.github.io/contribute/values.html).
Use the following rules during development and at each milestone.

- Search the pinned Mathlib, `Common/Mathlib`, existing SpinGlass APIs and the
  target `main` branch before adding an object or property. Search by its
  mathematical role as well as its name. Prefer an existing theorem, a short
  specialization, or an extension in the existing owner over a parallel API.
- Give each mathematical object one canonical definition at the lowest suitable
  dependency layer. General analysis and probability belong in `Common/Mathlib`
  when absent from Mathlib; Parisi-specific bridges stay here. In particular,
  compare `Analytic/` with the existing heat, Cole-Hopf and cascade layers.
  Moving or renaming the former `ARISTOTLE.lean` does not establish deduplication.
- A definition must not conceal an unproved identification, regularity result,
  integrability condition, normalization, or desired conclusion. Inspect
  structures, predicates, instances and chosen witnesses as well as `def`s.
  Prove their connection to the actual recursion or probability law. A bundle
  assuming the target estimate is a conditional interface, not its proof.
- State derivative results using `HasDerivAt`, `HasDerivWithinAt`, `deriv`,
  `derivWithin` or `iteratedDeriv` of the original object as appropriate.
  Explicit response formulas may be useful auxiliaries, but need proved
  derivative identities on their claimed domains. Naming a formula a derivative
  does not discharge differentiability, including at zero mass or variance.
- Consolidate special cases through general statements: deterministic fields
  through Dirac laws, root/right insertions through a level parameter where
  appropriate, and hypothesis variants through the weakest useful theorem.
  Retain a wrapper only for a concrete usability or compatibility reason;
  avoid copying its definition or proof. Remove superseded code after migrating
  consumers and updating the index.
- Check hypothesis bundles against their sources and construct representative
  model instances. Use standard predicates such as `IsMinOn` where applicable,
  keeping any separate admissibility requirement. Do not replace endpoint
  derivative assumptions with stronger smoothness merely to simplify an API.

## Milestone review before a PR

After reaching a milestone, review its entire diff before opening a PR to
SpinGlass. Proof completion and library integration are separate checks.

- Account for every new definition: reuse, specialize, move, remove, or retain
  with a mathematical reason. Review duplicate properties as well as objects.
- Record the canonical owners and any compatibility bridges; check that no
  proof obligation moved into a definition, bundle or final theorem hypothesis.
- Record source theorem/equation references and check assumption/conclusion
  strength, endpoint cases, and representative applications.
- Run the validation below for changed owners and consumers, including Common
  modules when moved. Record actual commands and results, remaining limitations,
  and the next task. Historical builds do not validate a new refactor.

The concrete review targets and acceptance conditions are maintained once in
[the consolidation backlog](Docs/EDITING_PLAN.md#consolidation-backlog).

## Style

Follow mathlib's [naming](https://leanprover-community.github.io/contribute/naming.html)
and [style](https://leanprover-community.github.io/contribute/style.html)
conventions, with the repository's pinned toolchain and options. Keep local
rules small: descriptive mathematical names, explicit binder and result types,
two-space proof indentation, lines normally within 100 characters, and direct
imports of declaration owners. Use `snake_case` for theorem names,
`UpperCamelCase` for types and predicates, and `lowerCamelCase` for other data,
respecting established Mathlib names. New code belongs in the namespace of its
mathematical owner; compatibility namespaces need not dictate new names.
Declare proved propositions as theorems with explicit result types.
Document public definitions and main results concisely, with source references
where applicable. Prefer readable proofs and useful supporting lemmas over
tactic compression. Add automation attributes only with a clear intended use.

## Work efficiently

- Keep task edits focused on `SpinGlass/Parisi/`. For API consolidation, the
  user's requested moves to `Common/Mathlib` and necessary consumer updates
  are in scope when they remove duplication or give a generic result its proper
  owner. Do not edit installed dependencies. Read-only checks outside this
  directory and build outputs in the existing parent cache are allowed.
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
- Keep the appropriate owner namespace, explicit binders, and repository Lean options.
  Put book theorem/equation references in bridge-lemma docstrings.
- Do not add `sorry`, `admit`, project axioms, or unsafe proof shortcuts. Audit the
  transitive dependency cone, including helpers outside this directory.
- On Windows, set PowerShell `$OutputEncoding` to UTF-8 before piping Unicode
  source-editing scripts to Python; use `python -X utf8` and inspect the diff.
- On handoff, record the exact declaration completed, checks actually run, any
  blocker, and the next smallest lemma in the plan. Source inspection is not a
  successful build.

## Validation

Build each changed leaf and its relevant consumers. The local
[.parisi-lean.ps1](.parisi-lean.ps1) wrapper resolves the repository root from its
own location and runs Lake there, keeping Git ownership configuration local to
the command. For complete coverage, run from the repository root:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File SpinGlass/Parisi/.parisi-lean.ps1 build
powershell -NoProfile -ExecutionPolicy Bypass -File SpinGlass/Parisi/.parisi-lean.ps1 build SpinGlass.Parisi.ParisiLowerBound
git diff --check
rg -n '\b(sorry|admit|axiom|unsafe)\b' SpinGlass/Parisi --glob '*.lean'
```

From `SpinGlass/Parisi/`, build the capstone with:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File ./.parisi-lean.ps1 build SpinGlass.Parisi.ParisiLowerBound
```

SpinGlass.lean imports SpinGlass/Parisi.lean, whose convenience import covers
all modules under this folder, including the capstone and analytic library.
Proof leaves must still import their declaration owners, avoiding umbrella
imports and cycles.

Inspect source-scan hits; comments and declarations differ. Compilation can
succeed with a proof hole. Use `#print axioms` on the capstone and changed public
helpers to check their transitive foundations; `propext`, `Classical.choice` and
`Quot.sound` are expected. No new project axiom or `sorryAx` is allowed.

Toolchain and cache locations come from lean-toolchain and lakefile.toml. Build
outputs live in the parent `.lake/spinglass` cache; do not relocate dependencies.
For documentation-only changes, check links, declaration/module names and
`git diff --check`; a full rebuild is unnecessary.

Completion requires preserved capstone contracts, successful leaf and consumer
builds, the foundation audit, source fidelity, the milestone API review, and
accurate architecture/status documents. Documentation-only changes use the
lighter checks above and do not establish completion of the consolidation backlog.
